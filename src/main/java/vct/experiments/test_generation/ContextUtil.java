package vct.experiments.test_generation;

import org.antlr.v4.runtime.ParserRuleContext;
import scala.NotImplementedError;
import vct.antlr4.generated.JavaParser;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Stack;

import static vct.experiments.test_generation.ConstraintUtil.getSurroundingClass;
import static vct.experiments.test_generation.TestGenerationUtil.throwForChangedParser;

public class ContextUtil {

	/**
	 * Don't use, this is a static util class
	 */
	private ContextUtil() {}

	/**
	 * @param context
	 * @return false if context is null
	 */
	public static boolean isStatic(JavaParser.MethodDeclarationContext context) {
		if (context == null) return false;

		if (!(context instanceof JavaParser.MethodDeclaration0Context)) return false;

		if (!(context.parent instanceof JavaParser.MemberDeclarationContext)) return false;
		var memberdecl = (JavaParser.MemberDeclarationContext) context.getParent();

		if (!(memberdecl.getParent() instanceof JavaParser.ClassBodyDeclarationContext)) return false;
		var classBodyDecl = (JavaParser.ClassBodyDeclarationContext) memberdecl.getParent();

		if (!(classBodyDecl instanceof JavaParser.ClassBodyDeclaration2Context)) return false;

		var modifier = ((JavaParser.ClassBodyDeclaration2Context) classBodyDecl).modifier();

		return modifier
				.stream()
				.filter(JavaParser.Modifier0Context.class::isInstance)
				.map(JavaParser.Modifier0Context.class::cast)
				.map(JavaParser.Modifier0Context::classOrInterfaceModifier)
				.filter(JavaParser.ClassOrInterfaceModifier1Context.class::isInstance)
				.map(JavaParser.ClassOrInterfaceModifier1Context.class::cast)
				.map(JavaParser.ClassOrInterfaceModifier1Context::STATIC)
				.anyMatch(Objects::nonNull);
	}

	public static String getClassName(JavaParser.ClassBodyContext classBodyContext) {
		if (classBodyContext == null) return "null_ClassBodyContext";

		if (!(classBodyContext.getParent() instanceof JavaParser.ClassDeclaration0Context)) return "Invalid_ClassBodyContext";

		var classDecl = ((JavaParser.ClassDeclaration0Context) classBodyContext.getParent());

		if (classDecl.javaIdentifier() == null) {
			return "null_ClassIdentifier";
		}

		return getStringValue(classDecl.javaIdentifier());
	}

	public static String getStringValue(JavaParser.JavaIdentifierContext ctx) {
		if (ctx == null) return "null_IdentifierContext";

		if (!(ctx instanceof JavaParser.JavaIdentifier1Context)) return "Invalid_NotBareIdentifier";

		var identifier = ((JavaParser.JavaIdentifier1Context) ctx).Identifier();

		return identifier.getSymbol().getText();
	}

	public static String getMethodName(JavaParser.MethodDeclarationContext method) {
		if (method == null) return "Null_MethodName";

		if (!(method instanceof JavaParser.MethodDeclaration0Context)) return "Invalid_MethodDeclClass";

		return getStringValue(((JavaParser.MethodDeclaration0Context) method).javaIdentifier());
	}

	public static List<JavaParser.FormalParameterContext> getParams(JavaParser.MethodDeclarationContext method) {
		assert method instanceof JavaParser.MethodDeclaration0Context;
		var params = ((JavaParser.MethodDeclaration0Context) method).formalParameters();
		assert params instanceof JavaParser.FormalParameters0Context;
		var paramListctx = ((JavaParser.FormalParameters0Context) params).formalParameterList();

		var list = new ArrayList<JavaParser.FormalParameterContext>();
		if (paramListctx == null) {
			// There is no paramlist
			return list;
		}

		if (!(paramListctx instanceof JavaParser.FormalParameterList1Context)) {
			throw new NotImplementedError("We don't support VarArgs yet.");
		}

		var current = ((JavaParser.FormalParameterList1Context) paramListctx).initFormalParameterList();

		while (current != null) {
			if (current instanceof JavaParser.InitFormalParameterList0Context) {
				list.add(((JavaParser.InitFormalParameterList0Context) current).formalParameter());
				break;

			} else if (current instanceof JavaParser.InitFormalParameterList1Context) {
				list.add(((JavaParser.InitFormalParameterList1Context) current).formalParameter());
				current = ((JavaParser.InitFormalParameterList1Context) current).initFormalParameterList();
			} else {
				throw new NotImplementedError("The Java Parser changed! This is not able to happen at the point of writing.");
			}

		}
		return list;
		// The tree here is somewhat like a linked list.
		//  Every formalParamList either has a
		//    param and a list, or a
		//    param and null
	}

	public static String getType(ParserRuleContext context) {
		if (context instanceof JavaParser.FormalParameterContext) {
			return getType((JavaParser.FormalParameterContext) context);
		} else if (context instanceof JavaParser.VariableDeclaratorContext) {
			return getType((JavaParser.VariableDeclaratorContext) context);
		}

		throw new IllegalStateException("Unsupported GetType call for parserRuleContext of type " + context.getClass());
	}

	public static String getType(JavaParser.VariableDeclaratorContext context) {
		if (!(context instanceof JavaParser.VariableDeclarator0Context)) throwForChangedParser(context);

		var declarators = context.getParent();
		if (!(declarators instanceof JavaParser.VariableDeclaratorsContext)) throwForChangedParser(declarators);

		var fieldDeclOrLocalDecl = declarators.getParent();

		// Both fieldDecl and LocalDecl have the type in them.

		var typeCtx = fieldDeclOrLocalDecl.getRuleContext(JavaParser.TypeContext.class,0);
		if (typeCtx == null) throwForChangedParser(fieldDeclOrLocalDecl);

		return getType(typeCtx);
	}

	public static String getType(JavaParser.FormalParameterContext parameterContext) {
		if (!(parameterContext instanceof JavaParser.FormalParameter0Context)) {
			return "INVALID_FORMAL_PARAM_CONTEXT_NO_TYPE_EXTRACTABLE";
		}
		var typeContext = ((JavaParser.FormalParameter0Context) parameterContext).type();

		return getType(typeContext);
	}

	public static String getType(JavaParser.TypeContext context) {
		if (!(context instanceof JavaParser.Type2Context)) {
			throw new NotImplementedError("Cannot parse type of Formal Parameter, is not a primitive.");
		}

		String type = ((JavaParser.Type2Context) context).primitiveType().getText();
		var dimsctx = ((JavaParser.Type2Context) context).dims();
		if (dimsctx == null) {
			return type; // No dimensioncontext mean not an array.
		}
		return type + dimsctx.getText();
	}

	public static String getValueInitializer(JavaParser.FormalParameterContext param, Object requiredValue) {
		if (requiredValue == null) {
			return "null";
		} else if (requiredValue instanceof Boolean ||
				requiredValue instanceof Byte ||
				requiredValue instanceof Short ||
				requiredValue instanceof Integer ||
				requiredValue instanceof Long ||
				requiredValue instanceof Double) {
			return requiredValue.toString();
		}else if (requiredValue instanceof Float) {
			return requiredValue + "F";
		} else if (requiredValue instanceof Character) {
			return "'" + requiredValue + "'";
		} else if (requiredValue instanceof String) {
			return '"' + (String) requiredValue + '"';
		}
		// This may just be out of scope.
		//  There are loads of things that do this, they are all huge. (Think frameworks like Spring etc.)
		throw new NotImplementedError(String.format("No way of getting value init for param %s and value %s.", param, requiredValue));
	}

	public static Object getRequiredValue(String paramName,
	                                      ParserRuleContext param,
	                                      Stack<List<ProgramFlowConstraint>> constraints) {
		if (isGoal(paramName, constraints)) {
			if (hasNoDirectRequirements(paramName, constraints)) {
				return null; // For now we hardcode this
			}
			// TODO: the case where the only requirements are null
			throw new NotImplementedError("Cannot get required value for goal that must be null but also has other requirements.");
		} else if (hasNoDirectRequirements(paramName, constraints)) {
			return getDefaultValueForType(getType(param));
		} else {
			throw new NotImplementedError("Only made support from reqValue of goal for now.");
		}
	}

		// TODO: constr.constrains impl does not work yet
	public static boolean hasNoDirectRequirements(String param, Stack<List<ProgramFlowConstraint>> constraints) {
//		for (List<ProgramFlowConstraint> scope : constraints) {
//			for (ProgramFlowConstraint constr : scope) {
//				if (constr.constrains(param)) {
//					return false;
//				}
//			}
//		}
		return true;
	}

	public static Object getDefaultValueForType(String type) {
		return switch (type) {
			case "string":
				yield (String) "";
			case "int":
				yield (Integer) 1;
			case "long":
				yield (Long) 1L;
			case "short":
				yield Short.valueOf("1");
			case "byte":
				yield Byte.valueOf("1");
			case "boolean":
				yield Boolean.TRUE;
			case "char":
				yield (Character) 'a';
			case "float":
				yield (Float) 0.0F;
			case "double":
				yield (Double) 0.0;
			default:
				throw new IllegalStateException("Unexpected value for getDefaultValue: " + type);
		};
	}

	public static boolean isGoal(String varName, Stack<List<ProgramFlowConstraint>> constraints) {
		var actualGoal = ConstraintUtil.getGoal(constraints);

		var goalVarName = getName(actualGoal.context);

		// Since java has unique local variable names we can just compare these and ignore scopes.
		return Objects.equals(goalVarName, varName);
	}

	public static String getName(JavaParser.Statement11Context context) {
		if (context.expression() == null) {
			return ""; // bare return statement, never happens for us for now
		}
		return getName(context.expression());
	}

	public static String getName(JavaParser.ExpressionContext context) {
		if (!(context instanceof JavaParser.Expression1Context)) {
			throw new NotImplementedError("Can only get name from bare expressions");
		}
		var prim = ((JavaParser.Expression1Context) context).primary();

		if (!(prim instanceof JavaParser.Primary4Context)) {
			throw new NotImplementedError("Can only get name from bare name Primary context");
		}

		return getName(((JavaParser.Primary4Context) prim).javaIdentifier());
	}

	public static String getName(JavaParser.JavaIdentifierContext context) {
		if (!(context instanceof JavaParser.JavaIdentifier1Context)) {
			throw new NotImplementedError("Can only get name from bare identifier contexts");
		}

		return ((JavaParser.JavaIdentifier1Context) context).Identifier().getText().strip();
	}

	public static String getName(JavaParser.FormalParameter0Context context) {
		if (!(context.variableDeclaratorId() instanceof JavaParser.VariableDeclaratorId0Context)) {
			throw new NotImplementedError("The Java Parser changed! This is not able to happen at the point of writing.");
		}
		return getName((JavaParser.VariableDeclaratorId0Context) context.variableDeclaratorId());
	}

	public static String getName(JavaParser.VariableDeclaratorId0Context context) {
		return getName(context.javaIdentifier());
	}

	public static String getName(ParserRuleContext context) {
		if (context instanceof JavaParser.Statement11Context) {
			return getName((JavaParser.Statement11Context) context);
		} else if (context instanceof JavaParser.FormalParameter0Context) {
			return getName((JavaParser.FormalParameter0Context) context);
		} else if (context instanceof JavaParser.VariableDeclarator0Context) {
			return getName((JavaParser.VariableDeclaratorId0Context) ((JavaParser.VariableDeclarator0Context) context).variableDeclaratorId());
		}

		throw new NotImplementedError("Cannot get name for this object of type " + context.getClass().toString());
	}

	// TODO: We use a very ugly syntax for throwing on Parser change here. Make helper?
	/**
	 * @param ctx an expression, assumed to be of type `this.name`. Which is more specific than the type can portray.
	 * @return null if none, else the varDeclCtx with the same name as the name in `this.name` for the input.
	 */
	public static JavaParser.VariableDeclaratorContext getInstanceDecl(JavaParser.Expression2Context ctx) {
		var klass = getSurroundingClass(ctx);

		if (!( klass instanceof JavaParser.ClassBody0Context)) throw new IllegalStateException("Java Parser changed surrounding the ClassBodyContext.");

		var body = ((JavaParser.ClassBody0Context) klass).classBodyDeclaration();
		var varname = getName(ctx.javaIdentifier());

		for (JavaParser.ClassBodyDeclarationContext bodyDeclarationContext : body) {
			if (!(bodyDeclarationContext instanceof JavaParser.ClassBodyDeclaration2Context)) {
				continue;
			}
			// We are a member decl
			var memberdecl = ((JavaParser.ClassBodyDeclaration2Context) bodyDeclarationContext).memberDeclaration();
			if (!(memberdecl instanceof JavaParser.MemberDeclaration2Context)) {
				continue;
			}
			var fieldDecl = ((JavaParser.MemberDeclaration2Context) memberdecl).fieldDeclaration();
			if (!(fieldDecl instanceof JavaParser.FieldDeclaration0Context)) throw new IllegalStateException("Java Parser changed surrounding the FieldDeclarationContext.");

			var vars = ((JavaParser.FieldDeclaration0Context) fieldDecl).variableDeclarators();
			if (!(vars instanceof JavaParser.VariableDeclarators0Context)) throw new NotImplementedError("No support for comma separated field decls.");

			var declarated = ((JavaParser.VariableDeclarators0Context) vars).variableDeclarator();
			if (!(declarated instanceof JavaParser.VariableDeclarator0Context)) throw new IllegalStateException("Java Parser changed surrounding the VariableDeclaratorContext.");

			var declid = ((JavaParser.VariableDeclarator0Context) declarated).variableDeclaratorId();
			if (!(declid instanceof JavaParser.VariableDeclaratorId0Context)) throw new IllegalStateException("Java Parser changed surrounding the VariableDeclaratorId0Context.");

			var declName = getName((JavaParser.VariableDeclaratorId0Context) declid);

			if (Objects.equals(varname, declName)) {
				return declarated;
			}

		}
		return null;
	}

}
