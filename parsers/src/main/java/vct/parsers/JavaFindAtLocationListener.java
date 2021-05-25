package vct.parsers;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import vct.antlr4.generated.JavaParserBaseListener;

import java.util.Optional;

/**
 * A listener that can find a ParserRuleContext from a line and col index.
 */
public class JavaFindAtLocationListener extends JavaParserBaseListener {
	private final int line;
	private final int col;
	public ParserRuleContext result = null;

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

	private JavaFindAtLocationListener(int line, int col) {
		super();
		this.line = line;
		this.col = col;
	}

	@Override
	public void enterEveryRule(ParserRuleContext ctx) {
		// This overwrites previous hits. This is good since the "deepest" hit is the most specific in type.
		if (ctx.start.getLine() == line && ctx.start.getCharPositionInLine() == col)
			this.result = ctx;
	}
}
