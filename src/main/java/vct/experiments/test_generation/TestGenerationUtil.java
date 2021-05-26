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
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import static hre.lang.System.DebugException;
import static hre.lang.System.Output;

public class TestGenerationUtil {


	/**
	 * Don't use. All methods here are static.
	 */
	private TestGenerationUtil() {}

	/**
	 * @param line The line index that your wished context is at.
	 * @param col The Col index that you wished context is at. Antlr indexes the cols at 0, Origin appears to index to 1
	 * @param tree The tree to search below.
	 * @return Either a context if found, or null if not.
	 */
	public static Optional<ParserRuleContext> getAtLocation(int line, int col, ParseTree tree) {

		var listener = new JavaFindAtLocationListener(line, col);

		new ParseTreeWalker().walk(listener, tree);

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
	 * @param origin May be null.
	 * @return The ParserRuleContext at this location. Empty if file not found, parser creation failed, or origin null.
	 */
	public static Optional<ParserRuleContext> getParseRuleFor(FileOrigin origin) {
		if (origin == null) return Optional.empty();

		var file = getOrCreateFile(origin.getPath());

		var parser = parseFile(file);
		if (parser == null) return Optional.empty();

		return getAtLocation(origin.getFirstLine(), origin.getFirstColumn() - 1, parser.compilationUnit());
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
}
