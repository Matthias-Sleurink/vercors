package vct.experiments.test_generation;

import org.antlr.v4.runtime.ParserRuleContext;
import vct.antlr4.generated.JavaParserBaseListener;


/**
 * A listener that can find a ParserRuleContext from a line and col index.
 * Use the util method vct/experiments/test_generation/TestGenerationUtil;getAtLocation instead of this class.
 */
public class JavaFindAtLocationListener extends JavaParserBaseListener {
	private final int line;
	private final int col;
	public ParserRuleContext result = null;

	/**
	 * Don't use this. Use the util method at vct/experiments/test_generation/TestGenerationUtil;getAtLocation
	 */
	JavaFindAtLocationListener(int line, int col) {
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
