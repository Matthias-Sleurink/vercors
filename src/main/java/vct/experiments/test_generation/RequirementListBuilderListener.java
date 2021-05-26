package vct.experiments.test_generation;

import org.antlr.v4.runtime.ParserRuleContext;
import vct.antlr4.generated.JavaParser;
import vct.antlr4.generated.JavaParserBaseListener;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;
import java.util.concurrent.CancellationException;

import static hre.lang.System.Output;

// This may be easier with a list of Context classes and an instanceof check for all of those in the enterall?

// TODO: Make sure that multi method classes also work. (Flush when not found yet in a method?)
public class RequirementListBuilderListener extends JavaParserBaseListener {
	public static boolean contextMeansReverseNext(ParserRuleContext ctx) {return ctx instanceof ReverseNextRuleFakeContext;}
	/**
	 * When we enter a scope we do not yet know whether or not our result is inside this scope.
	 * Thus we make a stack of requirements, these are then popped and pushed when entering and exiting scopes.
	 */
	public Stack<List<ParserRuleContext>> requirements = new Stack<>();
	public ParserRuleContext endpoint;

	public RequirementListBuilderListener(ParserRuleContext endpoint) {
		this.endpoint = endpoint;
	}

	private void addReq(ParserRuleContext req) {
		this.requirements.peek().add(req);
	}

	private void popScope() {this.requirements.pop();}
	private void pushScope() {this.requirements.push(new ArrayList<>());}

	@Override
	public void enterEveryRule(ParserRuleContext ctx) {
//		Output("Rule: %s", ctx.getClass().toString());
		if (ctx.equals(endpoint)) {
			throw new CancellationException(String.format("Found result in %s.", this.getClass().toString()));
		}
	}

	@Override
	public void enterCompilationUnit0(JavaParser.CompilationUnit0Context ctx) {
		pushScope();
	}

	@Override
	public void exitCompilationUnit0(JavaParser.CompilationUnit0Context ctx) {
		popScope();
	}

	@Override
	public void enterMethodDeclaration0(JavaParser.MethodDeclaration0Context ctx) {
		pushScope();
	}

	@Override
	public void exitMethodDeclaration0(JavaParser.MethodDeclaration0Context ctx) {
		popScope();
	}

	@Override
	public void enterFormalParameter0(JavaParser.FormalParameter0Context ctx) {
		addReq(ctx); // Source
	}

	@Override
	public void enterVarargsFormalParameter0(JavaParser.VarargsFormalParameter0Context ctx) {
		addReq(ctx); // Source
	}

	@Override
	public void exitVariableDeclarator0(JavaParser.VariableDeclarator0Context ctx) {
		addReq(ctx); // Source
	}

	@Override // Assert
	public void enterStatement1(JavaParser.Statement1Context ctx) {
		addReq(ctx); // constraint
	}

	@Override
	public void enterStatement2(JavaParser.Statement2Context ctx) {
		// This is the entrypoint to an if statement
		pushScope();
		addReq(ctx.parExpression()); // this happening is assumed in enterElseBlock0
	}

	@Override
	public void exitStatement2(JavaParser.Statement2Context ctx) {
		// If this did not have an else block we pop here
		// If this does have an else block we handle that in the else context (Since we need to reverse the entry requirement etc)
		if (ctx.elseBlock() != null) {
			popScope();
		}
	}

	@Override
	public void enterElseBlock0(JavaParser.ElseBlock0Context ctx) {
		// This is the other side to an if block
		// We save the req for the if block and reverse it
		var reqToReverse = this.requirements.peek().get(0);
		popScope();
		pushScope();
		addReq(new ReverseNextRuleFakeContext());
		addReq(reqToReverse);
	}

	@Override
	public void exitElseBlock0(JavaParser.ElseBlock0Context ctx) {
		popScope();
	}
}
