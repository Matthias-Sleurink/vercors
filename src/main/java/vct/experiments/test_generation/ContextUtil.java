package vct.experiments.test_generation;

import vct.antlr4.generated.JavaParser;

import java.util.Objects;

import static hre.lang.System.Output;

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
}
