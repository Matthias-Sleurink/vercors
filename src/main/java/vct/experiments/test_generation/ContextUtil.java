package vct.experiments.test_generation;

import org.antlr.v4.runtime.ParserRuleContext;
import scala.NotImplementedError;
import vct.antlr4.generated.JavaParser;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Stack;

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

	public static String getType(JavaParser.FormalParameterContext parameterContext) {
		if (!(parameterContext instanceof JavaParser.FormalParameter0Context)) {
			return "INVALID_FORMAL_PARAM_CONTEXT_NO_TYPE_EXTRACTABLE";
		}

		var typeContext = ((JavaParser.FormalParameter0Context) parameterContext).type();

		if (!(typeContext instanceof JavaParser.Type2Context)) {
			throw new NotImplementedError("Cannot parse type of Formal Parameter, is not a primitive.");
		}

		String type = ((JavaParser.Type2Context) typeContext).primitiveType().getText();
		var dimsctx = ((JavaParser.Type2Context) typeContext).dims();
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

	public static Object getRequiredValue(JavaParser.FormalParameterContext param,
	                                      Stack<List<ProgramFlowConstraint>> constraints) {
		if (isGoal(param, constraints)) {
			if (hasNoDirectRequirements(param, constraints)) {
				return null; // For now we hardcode this
			}
			// TODO: the case where the only requirements are null
			throw new NotImplementedError("Cannot get required value for goal that must be null but also has other requirements.");
		} else if (hasNoDirectRequirements(param, constraints)) {
			return getDefaultValueForType(getType(param));
		} else {
			throw new NotImplementedError("Only made support from reqValue of goal for now.");
		}
	}

	public static boolean hasNoDirectRequirements(JavaParser.FormalParameterContext param, Stack<List<ProgramFlowConstraint>> constraints) {
		return true; // TODO: Will work on this tomorrow
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

	public static boolean isGoal(JavaParser.FormalParameterContext param, Stack<List<ProgramFlowConstraint>> constraints) {
		var actualGoal = ConstraintUtil.getGoal(constraints);

		var goalVarName = getName(actualGoal.context);
		var paramName = getName(param);

		// Since java has unique local variable names we can just compare these and ignore scopes.
		return Objects.equals(goalVarName, paramName);
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
		}

		throw new NotImplementedError("Cannot get name for this object of type " + context.getClass().toString());
	}
}
