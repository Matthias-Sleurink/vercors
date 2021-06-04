package vct.experiments.test_generation;

import hre.ast.BranchOrigin;
import hre.ast.FileOrigin;
import hre.ast.Origin;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import scala.NotImplementedError;
import vct.antlr4.generated.JavaParser;
import vct.antlr4.generated.LangJavaLexer;
import viper.api.ViperError;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.CancellationException;

import static hre.lang.System.*;
import static vct.experiments.test_generation.ConstraintUtil.*;
import static vct.experiments.test_generation.ContextUtil.*;

public class TestGenerationUtil {


	/**
	 * Don't use. All methods here are static.
	 */
	private TestGenerationUtil() {}


	/**
	 * @param error An error to generate a test for. Nothing will be generated for a null ViperError.
	 */
	public static void logTestFor(ViperError<Origin> error) {
		var generationType = getGenerationType(error);
		if (generationType == TestGenerationType.RETURN_CAN_BE_NULL) {
			logReturnCanBeNull(error);
		}
		// Other types of tests can be appended here.
	}

	/**
	 * Log a test to the `Output` for the RETURN_CAN_BE_NULL case.
	 *
	 * @param error May not be null. Assumed that this is a RETURN_CAN_BE_NULL ViperError.
	 */
	private static void logReturnCanBeNull(ViperError<Origin> error) {
		// Remember that for RETURN_CAN_BE_NULL origin 0 is the one that points at the return statement
		var fileOrigin = getFileOrigin(error.getOrigin(0));
		var file = getOrCreateFile(fileOrigin.getPath());
		var parser = parseFile(file);
		if (parser == null) {
			Output("Tried to generate a test of type RETURN_CAN_BE_NULL for a null ViperError.");
			return;
		}

		var compilationUnit = parser.compilationUnit();
		var reqStack = getRequirementsFor(fileOrigin.getFirstLine(), fileOrigin.getFirstColumn(), compilationUnit);
		if (reqStack == null) {
			Output("Was not able to generate requirements for ViperError for RETURN_CAN_BE_NULL test case.");
			return;
		}

//		for (var reqList : reqStack) {
//			for (var constraint : reqList) {
//				Output(constraint.repr(parser));
//			}
//		}

		var code = getCodeThatSatisfies(reqStack, compilationUnit);
		// Formatted code is uses two spaces for indents, as that is what vercors uses.
		if (code != null) {
			Output("Generated counterexample for the issue shown below:");
			var codeFormatted = new StringBuilder("class MainCounterexample {\n");
			codeFormatted.append("  public static void main(String[] args) {\n");
			for (var line : code.split("\n")) {
				codeFormatted.append("    ").append(line).append("\n"); // newlines are removed in the split
			}
			codeFormatted.append("  }\n");
			codeFormatted.append("}");
			Output(codeFormatted.toString());
		} else {
			Debug("Was not able to generate code for counterexample.");
		}

	}

	private static String getCodeThatSatisfies(Stack<List<ProgramFlowConstraint>> constraints, JavaParser.CompilationUnitContext file) {
		var goal = constraints.peek().get(constraints.peek().size() - 1);
		// In theory this is always true from the helper, but it's a good check to do.
		if (goal.type != ProgramFlowConstraint.Type.Goal) return null;

		var method = getSurroundingMethod(goal);

		StringBuilder code = new StringBuilder();
		int index = 0;
		for (var param : getParams(method)) {
			code.append(getType(param))
					.append(" ")
					.append("param")
					.append(index)
					.append(" = ")
					.append(getValueInitializer(getRequiredValue(getName(param), param, constraints)))
					.append(";\n");
			index++;
		}

		// if requirements of static vars {setup}

		if (!isStatic(method)) {
			code.append(getNewInstanceCode(getSurroundingClass(goal)));
			for (var instancevar : getInstanceVariables(constraints)) {
				code.append("instance")
						.append(".")
						.append(getName(instancevar))
						.append(" = ")
						.append(getValueInitializer(getRequiredValue(getName(instancevar), instancevar, constraints)))
						.append(";\n");
			}
		}

		code.append(getCallCode(constraints));
		code.append("// Above will be null. But there is a postcondition that claims it is not.");

		return code.toString();
	}


	private static String getCallCode(Stack<List<ProgramFlowConstraint>> constraints) {
		var goal = getGoal(constraints);

		var method = getSurroundingMethod(goal);

		StringBuilder baseText = new StringBuilder();
		if (isStatic(method)) {
			baseText.append(getClassName(getSurroundingClass(method)))
			.append(".");
		} else {
			// In reality we should probably check if this is not an existing global var.
			baseText.append("instance.");
		}
		baseText.append(getMethodName(method)).append("(");
		var params = getParams(method);

		if (params.size() == 0) {
			return baseText.append(");\n").toString();
		}
		// for all but the last
		for (int i = 0; i < params.size() - 1; i++) {
			baseText.append("param").append(i).append(", ");
		}

		return baseText.append("param")
										.append(params.size() - 1)
										.append(");\n")
										.toString();
	}

	/**
	 * @param ctx Assumed that this class has the default constructor
	 * @return ends in newline, name of instance is "instance"
	 */
	public static String getNewInstanceCode(JavaParser.ClassBodyContext ctx) {
		return String.format("%s instance = new %s();\n", getClassName(ctx), getClassName(ctx));
	}

	/**
	 * @param line Raw line number from an origin
	 * @param col Raw col index from an origin
	 * @param tree The tree to search below.
	 * @return If possible, a stack of lists with requirements as ParserRuleContexts
	 */
	private static Stack<List<ProgramFlowConstraint>> getRequirementsFor(int line, int col, ParseTree tree) {
		var endpoint = getAtLocation(line, col, tree);
		if (endpoint.isEmpty()) {
			return null;
		}

		var reqBuilder = new RequirementListBuilderListener(endpoint.get());

		try {
			ParseTreeWalker.DEFAULT.walk(reqBuilder, tree);
			return null;
			// When the listener has found all the results it wants it throws a CancellationException.
		} catch (CancellationException e) {
			// Found the wanted results
			return reqBuilder.requirements;
		}
	}


	/**
	 * @param line The line index that your wished context is at.
	 * @param col The Col index that your wished context is at. Handles that antlrs indexes start at 0 and origins at 1
	 * @param tree The tree to search below.
	 * @return Either a context if found, or null if not.
	 */
	public static Optional<ParserRuleContext> getAtLocation(int line, int col, ParseTree tree) {
		var listener = new JavaFindAtLocationListener(line, col - 1);

		ParseTreeWalker.DEFAULT.walk(listener, tree);

		return Optional.ofNullable(listener.result);
	}

	private static final Map<Path, File> LoadedFileCache = new HashMap<>();

	/**
	 * @param path Nonnull
	 * @return The cached or created file for said path. Does no checking for existence etc.
	 */
	private static File getOrCreateFile(Path path) {
		if (!LoadedFileCache.containsKey(path)) {
			LoadedFileCache.put(path, path.toFile());
		}

		return LoadedFileCache.get(path);
	}

	/**
	 * Note that this method takes into account that the FileOrigins getFirstColumn appears to be 1 indexed
	 *  where the col for the parser rule is 0 indexed.
	 *
	 * This does not give access to the parsers result after this.
	 *  Thus it cannot be used with Trees from different parsers elements.
	 *
	 * @param origin May be null.
	 * @return The ParserRuleContext at this location. Empty if file not found, parser creation failed, or origin null.
	 */
	public static Optional<ParserRuleContext> getParseRuleFor(FileOrigin origin) {
		if (origin == null) return Optional.empty();

		var file = getOrCreateFile(origin.getPath());

		var parser = parseFile(file);
		if (parser == null) return Optional.empty();

		return getAtLocation(origin.getFirstLine(), origin.getFirstColumn(), parser.compilationUnit());
	}

	/**
	 * @param file A file to get a parser for. IOExceptions are accounted for.
	 * @return Null if reading the file causes an IOException.
	 */
	public static JavaParser parseFile(File file) {
		Lexer lexer;
		try {
			lexer = new LangJavaLexer(CharStreams.fromStream(new FileInputStream(file)));
		} catch (IOException e) {
			DebugException(e);
			Output("Couldn't read input file again. See debug output for more info.");
			return null;
		}
		CommonTokenStream tokens = new CommonTokenStream(lexer);

		return new JavaParser(tokens);
	}

	/**
	 * A best effort basis attempt to finding a FileOrigin from a more generic Origin.
	 * Handles exactly as much as I need for this project. Extendable to do more if needed.
	 *
	 * @param origin The origin to find a nested FileOrigin inside.
	 * @return A fileOrigin. Always. Throws NotImplementedError when it doesn't know how.
	 */
	public static FileOrigin getFileOrigin(Origin origin) {
		if (origin instanceof FileOrigin) {
			return (FileOrigin) origin;
		} else if (origin instanceof BranchOrigin) {
			return getFileOrigin(((BranchOrigin) origin).base);
		}
		throw new NotImplementedError(
				String.format("Getting FileOrigin for %s is not yet supported.", origin.getClass().toString()));
	}

	/**
	 * Looks at the error to find out what test should be generated for it.
	 *
	 * @param error This errors contents, cause, and location are looked at.
	 * @return The type of test that needs to be generated for this error
	 */
	public static TestGenerationType getGenerationType(ViperError<Origin> error) {
		if (error == null) return TestGenerationType.NONE;

		if (isReturnCanBeNull(error)) return TestGenerationType.RETURN_CAN_BE_NULL;

		return TestGenerationType.NONE;
	}

	// This is somewhat long and cursed, really not that great code, but it works for any example I could thing of
	/**
	 * @param error A nonnull ViperError
	 * @return True if this error should have a RETURN_CAN_BE_NULL TestGenerationType
	 */
	private static boolean isReturnCanBeNull(ViperError<Origin> error) {
		if (error.getExtraCount() < 1) return false;

		var fileOrigin = getFileOrigin(error.getOrigin(0));

		var filename = fileOrigin.getPath().toFile().getName();
		if (!(filename.endsWith("java") || filename.endsWith("java8") || filename.endsWith("java7"))) {
			// This follows the allowed extensions in `vct/main/Parsers;getParser(String)`
			return false;
		}

		var opt_parseRule = getParseRuleFor(fileOrigin);

		if (opt_parseRule.isEmpty()) return false;

		if (opt_parseRule.get().getToken(JavaParser.RETURN, 0) == null) {
			return false;
		}
		// we know now that the first origin is on a return statement

		if (error.getExtraCount() < 2) return false;
		fileOrigin = getFileOrigin(error.getOrigin(1));
		opt_parseRule = getParseRuleFor(fileOrigin);

		if (opt_parseRule.isEmpty()) return false;

		if (!(opt_parseRule.get() instanceof JavaParser.ValReservedContext)) return false;

		var valReserved = (JavaParser.ValReservedContext) opt_parseRule.get();

		if (valReserved.getToken(JavaParser.RESULT, 0) == null) return false;
		// This is a vercors message about the result

		// This is how this part of the tree should look:
		/*

    (expression
        (expression
            (primary
                (javaIdentifier
                    (valReserved \result) // This is var valReserved
                )
            )
        )
        !=
        (expression
            (primary
                (literal null)
            )
        )
    )
		 */
		//                                                      javaIdentifier primary
		var supposedPrimaryContext = valReserved.getParent()   .getParent();
		if (! (supposedPrimaryContext instanceof JavaParser.PrimaryContext)) return false;

		//                                                        (Contains the primary)
    //                                                                    expression  expression
		var supposedExpressionContext = supposedPrimaryContext.getParent().getParent();
		if (! (supposedExpressionContext instanceof JavaParser.ExpressionContext)) return false;

		// This is either a NOTEQUAL, or EQUAL, or other context, we only want the ones that are NOTEQUAL
		if (supposedExpressionContext.getToken(JavaParser.NOTEQUAL, 0) == null) return false;
		var otherSide = supposedExpressionContext.getRuleContext(JavaParser.ExpressionContext.class,1);
		var supposedOtherSidePrimaryContext = otherSide.getChild(0);

		if (! (supposedOtherSidePrimaryContext instanceof JavaParser.PrimaryContext)) return false;
		var primContext = (JavaParser.PrimaryContext) supposedOtherSidePrimaryContext;

		var supposedLiteral = primContext.getChild(0);
		if (! (supposedLiteral instanceof JavaParser.LiteralContext)) return false;

		var literal = (JavaParser.LiteralContext) supposedLiteral;

		var supposedNullNode = literal.getToken(JavaParser.NullLiteral, 0);
		if (supposedNullNode == null) return false;

		// This whole thing was to walk a little up and then down the tree to find out if we have the a contract like:
		//@ ensures \result != null;

		return true;
	}

	public static void throwForChangedParser(Object shouldNotExist) {
		throw new IllegalStateException("Java parser appears to have changed! This type should not exist: " + shouldNotExist.getClass());
	}

}
