package vct.experiments.test_generation;

import org.antlr.v4.runtime.ParserRuleContext;
import vct.antlr4.generated.JavaParser;

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

}
