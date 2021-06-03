package vct.experiments.test_generation;

import org.antlr.v4.runtime.ParserRuleContext;
import scala.NotImplementedError;
import vct.antlr4.generated.JavaParser;

import java.security.InvalidParameterException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Stack;

import static vct.experiments.test_generation.ContextUtil.getInstanceDecl;

public class ConstraintUtil {


	/**
	 * Don't use, this is a static util class
	 */
	private ConstraintUtil() {}


	/**
	 * @param constraint constraint.context == null -> null
	 * @return the first parent that is of type JavaParser.MethodDeclarationContext
	 */
	public static JavaParser.MethodDeclarationContext getSurroundingMethod(ProgramFlowConstraint constraint) {
		return getSurroundingMethod(constraint.context);
	}

	public static JavaParser.MethodDeclarationContext getSurroundingMethod(ParserRuleContext context) {
		if (context == null) {
			return null;
		}
		if (context instanceof JavaParser.MethodDeclarationContext) {
			return (JavaParser.MethodDeclarationContext) context;
		}
		return getSurroundingMethod(context.getParent());
	}

	public static JavaParser.ClassBodyContext getSurroundingClass(ProgramFlowConstraint constraint) {
		return getSurroundingClass(constraint.context);
	}

	public static JavaParser.ClassBodyContext getSurroundingClass(ParserRuleContext context) {
		if (context == null) {
			return null;
		}
		if (context instanceof JavaParser.ClassBodyContext) {
			return (JavaParser.ClassBodyContext) context;
		}
		return getSurroundingClass(context.getParent());
	}

	public static ProgramFlowConstraint getGoal(Stack<List<ProgramFlowConstraint>> constraints) {
		ProgramFlowConstraint constraint = constraints.peek().get(constraints.peek().size() - 1);

		if (constraint.type == ProgramFlowConstraint.Type.Goal) {
			return constraint;
		}
		throw new InvalidParameterException("ERROR: list of constraints did not have Goal at end.");
	}

	public static List<JavaParser.VariableDeclaratorContext> getInstanceVariables(
			Stack<List<ProgramFlowConstraint>> constraints) {
		var result = new ArrayList<JavaParser.VariableDeclaratorContext>();
		for (List<ProgramFlowConstraint> constraintList : constraints) {
			for (ProgramFlowConstraint programFlowConstraint : constraintList) {
				if (!programFlowConstraint.isTest()) continue;

				for (JavaParser.VariableDeclaratorContext declaratorContext : getInstanceDecls(programFlowConstraint)) {
					if (!result.contains(declaratorContext)) {
						result.add(declaratorContext);
					}
				}
			}
		}
		return result;
	}

	public static List<JavaParser.VariableDeclaratorContext> getInstanceDecls(ProgramFlowConstraint constraint) {
		var ctx = constraint.context;

		// We have a parseRuleContext that is of the Test types. So we can check for all the possible expressions inside and extract
		JavaParser.Expression2Context instanceDecl;
		if (ctx instanceof JavaParser.Statement1Context) {
			throw new NotImplementedError("No support for constraining instance variables with assert statements yet.");
		} else if (ctx instanceof JavaParser.ParExpression0Context) {
			if (((JavaParser.ParExpression0Context) ctx).expression() instanceof JavaParser.Expression2Context) {
				instanceDecl = (JavaParser.Expression2Context) ((JavaParser.ParExpression0Context) ctx).expression();
			} else {
				throw new NotImplementedError("Cannot drill down deeper into expressions to find `this.name` expressions yet. Got: "
						+ ((JavaParser.ParExpression0Context) ctx).expression().getClass());
			}
		} else if (ctx instanceof JavaParser.ForControl0Context) {
			// Enhanced for
				throw new NotImplementedError("Cannot drill down deeper into expressions to find `this.name` expressions yet.");
		} else if (ctx instanceof JavaParser.ForControl1Context) {
			// Old for
				throw new NotImplementedError("Cannot drill down deeper into expressions to find `this.name` expressions yet.");
		} else {
				throw new NotImplementedError("Unsupported context type for getInstanceDecls(ProgramFlowConstraint) " + ctx.getClass());
		}
		// TODO: make an actual recursive find all variables related method.

		var instance = getInstanceDecl(instanceDecl);
		if (instance == null) {
			return new ArrayList<>();
		}
		// This will become a longer array in the future
		//noinspection ArraysAsListWithZeroOrOneArgument
		return Arrays.asList(instance);
	}
}
