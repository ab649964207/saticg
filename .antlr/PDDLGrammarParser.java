// Generated from c:\Users\admin\Desktop\����\4.24\4.18\PDDLGrammar.g4 b4.9NTLR 4.9
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class PDDLGrammarParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.9", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		DOMAIN=1, PROBLEM=2, DEFINE=3, AGENTID=4, CONST=5, TYPE=6, PREDICATE=7, 
		ACTION=8, EVENT=9, EVENTS=10, PLDEGREE=11, EVENTMODEL=12, PARAMETER=13, 
		TERCONDITION=14, PRECONDITION=15, CONSTRAINT=16, RESPONSE=17, OBSERVATION=18, 
		MIN=19, MAX=20, NUMS=21, NORMAL=22, MISER=23, EFFECT=24, OBJECT=25, INC=26, 
		DEC=27, ASSIGN=28, AGENT=29, EITHER=30, OBJS=31, INIT=32, GOAL=33, LB=34, 
		RB=35, LSB=36, RSB=37, COLON=38, QM=39, POINT=40, UL=41, MINUS=42, PLUS=43, 
		MULT=44, DIV=45, MOD=46, EQ=47, NEQ=48, LT=49, LEQ=50, GT=51, GEQ=52, 
		AND=53, OR=54, NOT=55, ONEOF=56, IMPLY=57, FORALL=58, EXISTS=59, WHEN=60, 
		NAME=61, INTEGER=62, VAR=63, FUNSYM=64, WS=65;
	public static final int
		RULE_domain = 0, RULE_objectDefine = 1, RULE_typeDefine = 2, RULE_terconditionDefine = 3, 
		RULE_constraintDefine = 4, RULE_predicate = 5, RULE_types = 6, RULE_actionDefine = 7, 
		RULE_actionSymbol = 8, RULE_typeName = 9, RULE_emptyOrPreGD = 10, RULE_emptyOrEffect = 11, 
		RULE_listName = 12, RULE_listVariable = 13, RULE_oneofDefine = 14, RULE_gd = 15, 
		RULE_termAtomForm = 16, RULE_termLiteral = 17, RULE_constTerm = 18, RULE_term = 19, 
		RULE_effect = 20, RULE_cEffect = 21, RULE_condEffect = 22, RULE_pEffect = 23, 
		RULE_assignop = 24, RULE_problemName = 25, RULE_domainName = 26, RULE_agentDefine = 27, 
		RULE_objectDeclaration = 28, RULE_init = 29, RULE_constTermAtomForm = 30;
	private static String[] makeRuleNames() {
		return new String[] {
			"domain", "objectDefine", "typeDefine", "terconditionDefine", "constraintDefine", 
			"predicate", "types", "actionDefine", "actionSymbol", "typeName", "emptyOrPreGD", 
			"emptyOrEffect", "listName", "listVariable", "oneofDefine", "gd", "termAtomForm", 
			"termLiteral", "constTerm", "term", "effect", "cEffect", "condEffect", 
			"pEffect", "assignop", "problemName", "domainName", "agentDefine", "objectDeclaration", 
			"init", "constTermAtomForm"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'domain'", "'problem'", "'define'", "'agentid'", "'constants'", 
			"'type'", "'predicates'", "'action'", "'event'", "'events'", "'pldegree'", 
			"'eventmodel'", "'parameters'", "'tercondition'", "'precondition'", "'constraint'", 
			"'response'", "'observation'", "'min'", "'max'", "'numbers'", "'normal'", 
			"'miser'", "'effect'", "'object'", "'increase'", "'decrease'", "'assign'", 
			"'agent'", "'either'", "'objects'", "'init'", "'goal'", "'('", "')'", 
			"'['", "']'", "':'", "'?'", "'.'", "'_'", "'-'", "'+'", "'*'", "'/'", 
			"'%'", "'='", "'!='", "'<'", "'<='", "'>'", "'>='", "'and'", "'or'", 
			"'not'", "'oneof'", "'imply'", "'forall'", "'exists'", "'when'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "DOMAIN", "PROBLEM", "DEFINE", "AGENTID", "CONST", "TYPE", "PREDICATE", 
			"ACTION", "EVENT", "EVENTS", "PLDEGREE", "EVENTMODEL", "PARAMETER", "TERCONDITION", 
			"PRECONDITION", "CONSTRAINT", "RESPONSE", "OBSERVATION", "MIN", "MAX", 
			"NUMS", "NORMAL", "MISER", "EFFECT", "OBJECT", "INC", "DEC", "ASSIGN", 
			"AGENT", "EITHER", "OBJS", "INIT", "GOAL", "LB", "RB", "LSB", "RSB", 
			"COLON", "QM", "POINT", "UL", "MINUS", "PLUS", "MULT", "DIV", "MOD", 
			"EQ", "NEQ", "LT", "LEQ", "GT", "GEQ", "AND", "OR", "NOT", "ONEOF", "IMPLY", 
			"FORALL", "EXISTS", "WHEN", "NAME", "INTEGER", "VAR", "FUNSYM", "WS"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "PDDLGrammar.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public PDDLGrammarParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class DomainContext extends ParserRuleContext {
		public List<TerminalNode> LB() { return getTokens(PDDLGrammarParser.LB); }
		public TerminalNode LB(int i) {
			return getToken(PDDLGrammarParser.LB, i);
		}
		public TerminalNode DEFINE() { return getToken(PDDLGrammarParser.DEFINE, 0); }
		public TerminalNode DOMAIN() { return getToken(PDDLGrammarParser.DOMAIN, 0); }
		public TerminalNode NAME() { return getToken(PDDLGrammarParser.NAME, 0); }
		public List<TerminalNode> RB() { return getTokens(PDDLGrammarParser.RB); }
		public TerminalNode RB(int i) {
			return getToken(PDDLGrammarParser.RB, i);
		}
		public ObjectDefineContext objectDefine() {
			return getRuleContext(ObjectDefineContext.class,0);
		}
		public TypeDefineContext typeDefine() {
			return getRuleContext(TypeDefineContext.class,0);
		}
		public TerconditionDefineContext terconditionDefine() {
			return getRuleContext(TerconditionDefineContext.class,0);
		}
		public ConstraintDefineContext constraintDefine() {
			return getRuleContext(ConstraintDefineContext.class,0);
		}
		public List<ActionDefineContext> actionDefine() {
			return getRuleContexts(ActionDefineContext.class);
		}
		public ActionDefineContext actionDefine(int i) {
			return getRuleContext(ActionDefineContext.class,i);
		}
		public DomainContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_domain; }
	}

	public final DomainContext domain() throws RecognitionException {
		DomainContext _localctx = new DomainContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_domain);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(62);
			match(LB);
			setState(63);
			match(DEFINE);
			setState(64);
			match(LB);
			setState(65);
			match(DOMAIN);
			setState(66);
			match(NAME);
			setState(67);
			match(RB);
			setState(68);
			objectDefine();
			setState(69);
			typeDefine();
			setState(70);
			terconditionDefine();
			setState(71);
			constraintDefine();
			setState(75);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==LB) {
				{
				{
				setState(72);
				actionDefine();
				}
				}
				setState(77);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(78);
			match(RB);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ObjectDefineContext extends ParserRuleContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode COLON() { return getToken(PDDLGrammarParser.COLON, 0); }
		public TerminalNode OBJS() { return getToken(PDDLGrammarParser.OBJS, 0); }
		public ListVariableContext listVariable() {
			return getRuleContext(ListVariableContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public ObjectDefineContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_objectDefine; }
	}

	public final ObjectDefineContext objectDefine() throws RecognitionException {
		ObjectDefineContext _localctx = new ObjectDefineContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_objectDefine);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(80);
			match(LB);
			setState(81);
			match(COLON);
			setState(82);
			match(OBJS);
			setState(83);
			listVariable();
			setState(84);
			match(RB);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TypeDefineContext extends ParserRuleContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode COLON() { return getToken(PDDLGrammarParser.COLON, 0); }
		public TerminalNode TYPE() { return getToken(PDDLGrammarParser.TYPE, 0); }
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public TypeDefineContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeDefine; }
	}

	public final TypeDefineContext typeDefine() throws RecognitionException {
		TypeDefineContext _localctx = new TypeDefineContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_typeDefine);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(86);
			match(LB);
			setState(87);
			match(COLON);
			setState(88);
			match(TYPE);
			setState(89);
			typeName();
			setState(90);
			match(RB);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TerconditionDefineContext extends ParserRuleContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode COLON() { return getToken(PDDLGrammarParser.COLON, 0); }
		public TerminalNode TERCONDITION() { return getToken(PDDLGrammarParser.TERCONDITION, 0); }
		public EmptyOrPreGDContext emptyOrPreGD() {
			return getRuleContext(EmptyOrPreGDContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public TerconditionDefineContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_terconditionDefine; }
	}

	public final TerconditionDefineContext terconditionDefine() throws RecognitionException {
		TerconditionDefineContext _localctx = new TerconditionDefineContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_terconditionDefine);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(92);
			match(LB);
			setState(93);
			match(COLON);
			setState(94);
			match(TERCONDITION);
			setState(95);
			emptyOrPreGD();
			setState(96);
			match(RB);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ConstraintDefineContext extends ParserRuleContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode COLON() { return getToken(PDDLGrammarParser.COLON, 0); }
		public TerminalNode CONSTRAINT() { return getToken(PDDLGrammarParser.CONSTRAINT, 0); }
		public EmptyOrPreGDContext emptyOrPreGD() {
			return getRuleContext(EmptyOrPreGDContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public ConstraintDefineContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_constraintDefine; }
	}

	public final ConstraintDefineContext constraintDefine() throws RecognitionException {
		ConstraintDefineContext _localctx = new ConstraintDefineContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_constraintDefine);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(98);
			match(LB);
			setState(99);
			match(COLON);
			setState(100);
			match(CONSTRAINT);
			setState(101);
			emptyOrPreGD();
			setState(102);
			match(RB);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class PredicateContext extends ParserRuleContext {
		public TerminalNode NAME() { return getToken(PDDLGrammarParser.NAME, 0); }
		public PredicateContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_predicate; }
	}

	public final PredicateContext predicate() throws RecognitionException {
		PredicateContext _localctx = new PredicateContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_predicate);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(104);
			match(NAME);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TypesContext extends ParserRuleContext {
		public TerminalNode OBJECT() { return getToken(PDDLGrammarParser.OBJECT, 0); }
		public TerminalNode AGENT() { return getToken(PDDLGrammarParser.AGENT, 0); }
		public TerminalNode NAME() { return getToken(PDDLGrammarParser.NAME, 0); }
		public TypesContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_types; }
	}

	public final TypesContext types() throws RecognitionException {
		TypesContext _localctx = new TypesContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_types);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(106);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << OBJECT) | (1L << AGENT) | (1L << NAME))) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ActionDefineContext extends ParserRuleContext {
		public List<TerminalNode> LB() { return getTokens(PDDLGrammarParser.LB); }
		public TerminalNode LB(int i) {
			return getToken(PDDLGrammarParser.LB, i);
		}
		public List<TerminalNode> COLON() { return getTokens(PDDLGrammarParser.COLON); }
		public TerminalNode COLON(int i) {
			return getToken(PDDLGrammarParser.COLON, i);
		}
		public TerminalNode ACTION() { return getToken(PDDLGrammarParser.ACTION, 0); }
		public ActionSymbolContext actionSymbol() {
			return getRuleContext(ActionSymbolContext.class,0);
		}
		public List<TerminalNode> RB() { return getTokens(PDDLGrammarParser.RB); }
		public TerminalNode RB(int i) {
			return getToken(PDDLGrammarParser.RB, i);
		}
		public TerminalNode PARAMETER() { return getToken(PDDLGrammarParser.PARAMETER, 0); }
		public ListVariableContext listVariable() {
			return getRuleContext(ListVariableContext.class,0);
		}
		public TerminalNode PRECONDITION() { return getToken(PDDLGrammarParser.PRECONDITION, 0); }
		public EmptyOrPreGDContext emptyOrPreGD() {
			return getRuleContext(EmptyOrPreGDContext.class,0);
		}
		public TerminalNode EFFECT() { return getToken(PDDLGrammarParser.EFFECT, 0); }
		public EmptyOrEffectContext emptyOrEffect() {
			return getRuleContext(EmptyOrEffectContext.class,0);
		}
		public ActionDefineContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_actionDefine; }
	}

	public final ActionDefineContext actionDefine() throws RecognitionException {
		ActionDefineContext _localctx = new ActionDefineContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_actionDefine);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(108);
			match(LB);
			setState(109);
			match(COLON);
			setState(110);
			match(ACTION);
			setState(111);
			actionSymbol();
			setState(118);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,1,_ctx) ) {
			case 1:
				{
				setState(112);
				match(COLON);
				setState(113);
				match(PARAMETER);
				setState(114);
				match(LB);
				setState(115);
				listVariable();
				setState(116);
				match(RB);
				}
				break;
			}
			setState(123);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
			case 1:
				{
				setState(120);
				match(COLON);
				setState(121);
				match(PRECONDITION);
				setState(122);
				emptyOrPreGD();
				}
				break;
			}
			setState(128);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==COLON) {
				{
				setState(125);
				match(COLON);
				setState(126);
				match(EFFECT);
				setState(127);
				emptyOrEffect();
				}
			}

			setState(130);
			match(RB);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ActionSymbolContext extends ParserRuleContext {
		public TerminalNode NAME() { return getToken(PDDLGrammarParser.NAME, 0); }
		public ActionSymbolContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_actionSymbol; }
	}

	public final ActionSymbolContext actionSymbol() throws RecognitionException {
		ActionSymbolContext _localctx = new ActionSymbolContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_actionSymbol);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(132);
			match(NAME);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TypeNameContext extends ParserRuleContext {
		public TerminalNode NAME() { return getToken(PDDLGrammarParser.NAME, 0); }
		public TypeNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeName; }
	}

	public final TypeNameContext typeName() throws RecognitionException {
		TypeNameContext _localctx = new TypeNameContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_typeName);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(134);
			match(NAME);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EmptyOrPreGDContext extends ParserRuleContext {
		public EmptyOrPreGDContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_emptyOrPreGD; }
	 
		public EmptyOrPreGDContext() { }
		public void copyFrom(EmptyOrPreGDContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class PreGDBracketContext extends EmptyOrPreGDContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public PreGDBracketContext(EmptyOrPreGDContext ctx) { copyFrom(ctx); }
	}
	public static class IsGdContext extends EmptyOrPreGDContext {
		public GdContext gd() {
			return getRuleContext(GdContext.class,0);
		}
		public IsGdContext(EmptyOrPreGDContext ctx) { copyFrom(ctx); }
	}

	public final EmptyOrPreGDContext emptyOrPreGD() throws RecognitionException {
		EmptyOrPreGDContext _localctx = new EmptyOrPreGDContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_emptyOrPreGD);
		try {
			setState(139);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,4,_ctx) ) {
			case 1:
				_localctx = new IsGdContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(136);
				gd();
				}
				break;
			case 2:
				_localctx = new PreGDBracketContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(137);
				match(LB);
				setState(138);
				match(RB);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EmptyOrEffectContext extends ParserRuleContext {
		public EmptyOrEffectContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_emptyOrEffect; }
	 
		public EmptyOrEffectContext() { }
		public void copyFrom(EmptyOrEffectContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class IsEffectContext extends EmptyOrEffectContext {
		public EffectContext effect() {
			return getRuleContext(EffectContext.class,0);
		}
		public IsEffectContext(EmptyOrEffectContext ctx) { copyFrom(ctx); }
	}
	public static class EffectBracketContext extends EmptyOrEffectContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public EffectBracketContext(EmptyOrEffectContext ctx) { copyFrom(ctx); }
	}

	public final EmptyOrEffectContext emptyOrEffect() throws RecognitionException {
		EmptyOrEffectContext _localctx = new EmptyOrEffectContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_emptyOrEffect);
		try {
			setState(144);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,5,_ctx) ) {
			case 1:
				_localctx = new IsEffectContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(141);
				effect();
				}
				break;
			case 2:
				_localctx = new EffectBracketContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(142);
				match(LB);
				setState(143);
				match(RB);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListNameContext extends ParserRuleContext {
		public List<TerminalNode> NAME() { return getTokens(PDDLGrammarParser.NAME); }
		public TerminalNode NAME(int i) {
			return getToken(PDDLGrammarParser.NAME, i);
		}
		public TerminalNode MINUS() { return getToken(PDDLGrammarParser.MINUS, 0); }
		public TypesContext types() {
			return getRuleContext(TypesContext.class,0);
		}
		public ListNameContext listName() {
			return getRuleContext(ListNameContext.class,0);
		}
		public ListNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listName; }
	}

	public final ListNameContext listName() throws RecognitionException {
		ListNameContext _localctx = new ListNameContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_listName);
		int _la;
		try {
			setState(161);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,8,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(149);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==NAME) {
					{
					{
					setState(146);
					match(NAME);
					}
					}
					setState(151);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(153); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(152);
					match(NAME);
					}
					}
					setState(155); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==NAME );
				setState(157);
				match(MINUS);
				setState(158);
				types();
				setState(159);
				listName();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListVariableContext extends ParserRuleContext {
		public List<TerminalNode> VAR() { return getTokens(PDDLGrammarParser.VAR); }
		public TerminalNode VAR(int i) {
			return getToken(PDDLGrammarParser.VAR, i);
		}
		public TerminalNode MINUS() { return getToken(PDDLGrammarParser.MINUS, 0); }
		public TypesContext types() {
			return getRuleContext(TypesContext.class,0);
		}
		public ListVariableContext listVariable() {
			return getRuleContext(ListVariableContext.class,0);
		}
		public ListVariableContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listVariable; }
	}

	public final ListVariableContext listVariable() throws RecognitionException {
		ListVariableContext _localctx = new ListVariableContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_listVariable);
		int _la;
		try {
			setState(178);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,11,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(166);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==VAR) {
					{
					{
					setState(163);
					match(VAR);
					}
					}
					setState(168);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(170); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(169);
					match(VAR);
					}
					}
					setState(172); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==VAR );
				setState(174);
				match(MINUS);
				setState(175);
				types();
				setState(176);
				listVariable();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class OneofDefineContext extends ParserRuleContext {
		public TerminalNode ONEOF() { return getToken(PDDLGrammarParser.ONEOF, 0); }
		public List<TerminalNode> VAR() { return getTokens(PDDLGrammarParser.VAR); }
		public TerminalNode VAR(int i) {
			return getToken(PDDLGrammarParser.VAR, i);
		}
		public OneofDefineContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_oneofDefine; }
	}

	public final OneofDefineContext oneofDefine() throws RecognitionException {
		OneofDefineContext _localctx = new OneofDefineContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_oneofDefine);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(180);
			match(ONEOF);
			setState(182); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(181);
				match(VAR);
				}
				}
				setState(184); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==VAR );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class GdContext extends ParserRuleContext {
		public GdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_gd; }
	 
		public GdContext() { }
		public void copyFrom(GdContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class NotContext extends GdContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode NOT() { return getToken(PDDLGrammarParser.NOT, 0); }
		public GdContext gd() {
			return getRuleContext(GdContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public NotContext(GdContext ctx) { copyFrom(ctx); }
	}
	public static class OrContext extends GdContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode OR() { return getToken(PDDLGrammarParser.OR, 0); }
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public List<GdContext> gd() {
			return getRuleContexts(GdContext.class);
		}
		public GdContext gd(int i) {
			return getRuleContext(GdContext.class,i);
		}
		public OrContext(GdContext ctx) { copyFrom(ctx); }
	}
	public static class ImplyContext extends GdContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode IMPLY() { return getToken(PDDLGrammarParser.IMPLY, 0); }
		public List<GdContext> gd() {
			return getRuleContexts(GdContext.class);
		}
		public GdContext gd(int i) {
			return getRuleContext(GdContext.class,i);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public ImplyContext(GdContext ctx) { copyFrom(ctx); }
	}
	public static class AndContext extends GdContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode AND() { return getToken(PDDLGrammarParser.AND, 0); }
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public List<GdContext> gd() {
			return getRuleContexts(GdContext.class);
		}
		public GdContext gd(int i) {
			return getRuleContext(GdContext.class,i);
		}
		public AndContext(GdContext ctx) { copyFrom(ctx); }
	}
	public static class ForallContext extends GdContext {
		public List<TerminalNode> LB() { return getTokens(PDDLGrammarParser.LB); }
		public TerminalNode LB(int i) {
			return getToken(PDDLGrammarParser.LB, i);
		}
		public TerminalNode FORALL() { return getToken(PDDLGrammarParser.FORALL, 0); }
		public ListVariableContext listVariable() {
			return getRuleContext(ListVariableContext.class,0);
		}
		public List<TerminalNode> RB() { return getTokens(PDDLGrammarParser.RB); }
		public TerminalNode RB(int i) {
			return getToken(PDDLGrammarParser.RB, i);
		}
		public GdContext gd() {
			return getRuleContext(GdContext.class,0);
		}
		public ForallContext(GdContext ctx) { copyFrom(ctx); }
	}
	public static class ExistsContext extends GdContext {
		public List<TerminalNode> LB() { return getTokens(PDDLGrammarParser.LB); }
		public TerminalNode LB(int i) {
			return getToken(PDDLGrammarParser.LB, i);
		}
		public TerminalNode EXISTS() { return getToken(PDDLGrammarParser.EXISTS, 0); }
		public ListVariableContext listVariable() {
			return getRuleContext(ListVariableContext.class,0);
		}
		public List<TerminalNode> RB() { return getTokens(PDDLGrammarParser.RB); }
		public TerminalNode RB(int i) {
			return getToken(PDDLGrammarParser.RB, i);
		}
		public GdContext gd() {
			return getRuleContext(GdContext.class,0);
		}
		public ExistsContext(GdContext ctx) { copyFrom(ctx); }
	}
	public static class AtomContext extends GdContext {
		public TermAtomFormContext termAtomForm() {
			return getRuleContext(TermAtomFormContext.class,0);
		}
		public AtomContext(GdContext ctx) { copyFrom(ctx); }
	}

	public final GdContext gd() throws RecognitionException {
		GdContext _localctx = new GdContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_gd);
		int _la;
		try {
			setState(232);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,15,_ctx) ) {
			case 1:
				_localctx = new AtomContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(186);
				termAtomForm();
				}
				break;
			case 2:
				_localctx = new AndContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(187);
				match(LB);
				setState(188);
				match(AND);
				setState(190); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(189);
					gd();
					}
					}
					setState(192); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==LB );
				setState(194);
				match(RB);
				}
				break;
			case 3:
				_localctx = new OrContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(196);
				match(LB);
				setState(197);
				match(OR);
				setState(199); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(198);
					gd();
					}
					}
					setState(201); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==LB );
				setState(203);
				match(RB);
				}
				break;
			case 4:
				_localctx = new NotContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(205);
				match(LB);
				setState(206);
				match(NOT);
				setState(207);
				gd();
				setState(208);
				match(RB);
				}
				break;
			case 5:
				_localctx = new ImplyContext(_localctx);
				enterOuterAlt(_localctx, 5);
				{
				setState(210);
				match(LB);
				setState(211);
				match(IMPLY);
				setState(212);
				gd();
				setState(213);
				gd();
				setState(214);
				match(RB);
				}
				break;
			case 6:
				_localctx = new ExistsContext(_localctx);
				enterOuterAlt(_localctx, 6);
				{
				setState(216);
				match(LB);
				setState(217);
				match(EXISTS);
				setState(218);
				match(LB);
				setState(219);
				listVariable();
				setState(220);
				match(RB);
				setState(221);
				gd();
				setState(222);
				match(RB);
				}
				break;
			case 7:
				_localctx = new ForallContext(_localctx);
				enterOuterAlt(_localctx, 7);
				{
				setState(224);
				match(LB);
				setState(225);
				match(FORALL);
				setState(226);
				match(LB);
				setState(227);
				listVariable();
				setState(228);
				match(RB);
				setState(229);
				gd();
				setState(230);
				match(RB);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TermAtomFormContext extends ParserRuleContext {
		public TermAtomFormContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_termAtomForm; }
	 
		public TermAtomFormContext() { }
		public void copyFrom(TermAtomFormContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class EqualContext extends TermAtomFormContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode EQ() { return getToken(PDDLGrammarParser.EQ, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public EqualContext(TermAtomFormContext ctx) { copyFrom(ctx); }
	}
	public static class NEqualContext extends TermAtomFormContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode NEQ() { return getToken(PDDLGrammarParser.NEQ, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public NEqualContext(TermAtomFormContext ctx) { copyFrom(ctx); }
	}
	public static class LessThanEqualContext extends TermAtomFormContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode LEQ() { return getToken(PDDLGrammarParser.LEQ, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public LessThanEqualContext(TermAtomFormContext ctx) { copyFrom(ctx); }
	}
	public static class GreaterThanEqualContext extends TermAtomFormContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode GEQ() { return getToken(PDDLGrammarParser.GEQ, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public GreaterThanEqualContext(TermAtomFormContext ctx) { copyFrom(ctx); }
	}
	public static class PredicateAContext extends TermAtomFormContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public PredicateContext predicate() {
			return getRuleContext(PredicateContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public PredicateAContext(TermAtomFormContext ctx) { copyFrom(ctx); }
	}
	public static class LessThanContext extends TermAtomFormContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode LT() { return getToken(PDDLGrammarParser.LT, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public LessThanContext(TermAtomFormContext ctx) { copyFrom(ctx); }
	}
	public static class GreaterThanContext extends TermAtomFormContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode GT() { return getToken(PDDLGrammarParser.GT, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public GreaterThanContext(TermAtomFormContext ctx) { copyFrom(ctx); }
	}

	public final TermAtomFormContext termAtomForm() throws RecognitionException {
		TermAtomFormContext _localctx = new TermAtomFormContext(_ctx, getState());
		enterRule(_localctx, 32, RULE_termAtomForm);
		int _la;
		try {
			setState(280);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,17,_ctx) ) {
			case 1:
				_localctx = new PredicateAContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(234);
				match(LB);
				setState(235);
				predicate();
				setState(239);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << LB) | (1L << NAME) | (1L << INTEGER) | (1L << VAR))) != 0)) {
					{
					{
					setState(236);
					term();
					}
					}
					setState(241);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(242);
				match(RB);
				}
				break;
			case 2:
				_localctx = new EqualContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(244);
				match(LB);
				setState(245);
				match(EQ);
				setState(246);
				term();
				setState(247);
				term();
				setState(248);
				match(RB);
				}
				break;
			case 3:
				_localctx = new NEqualContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(250);
				match(LB);
				setState(251);
				match(NEQ);
				setState(252);
				term();
				setState(253);
				term();
				setState(254);
				match(RB);
				}
				break;
			case 4:
				_localctx = new LessThanContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(256);
				match(LB);
				setState(257);
				match(LT);
				setState(258);
				term();
				setState(259);
				term();
				setState(260);
				match(RB);
				}
				break;
			case 5:
				_localctx = new LessThanEqualContext(_localctx);
				enterOuterAlt(_localctx, 5);
				{
				setState(262);
				match(LB);
				setState(263);
				match(LEQ);
				setState(264);
				term();
				setState(265);
				term();
				setState(266);
				match(RB);
				}
				break;
			case 6:
				_localctx = new GreaterThanContext(_localctx);
				enterOuterAlt(_localctx, 6);
				{
				setState(268);
				match(LB);
				setState(269);
				match(GT);
				setState(270);
				term();
				setState(271);
				term();
				setState(272);
				match(RB);
				}
				break;
			case 7:
				_localctx = new GreaterThanEqualContext(_localctx);
				enterOuterAlt(_localctx, 7);
				{
				setState(274);
				match(LB);
				setState(275);
				match(GEQ);
				setState(276);
				term();
				setState(277);
				term();
				setState(278);
				match(RB);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TermLiteralContext extends ParserRuleContext {
		public TermAtomFormContext termAtomForm() {
			return getRuleContext(TermAtomFormContext.class,0);
		}
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode NOT() { return getToken(PDDLGrammarParser.NOT, 0); }
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public TermLiteralContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_termLiteral; }
	}

	public final TermLiteralContext termLiteral() throws RecognitionException {
		TermLiteralContext _localctx = new TermLiteralContext(_ctx, getState());
		enterRule(_localctx, 34, RULE_termLiteral);
		try {
			setState(288);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,18,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(282);
				termAtomForm();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(283);
				match(LB);
				setState(284);
				match(NOT);
				setState(285);
				termAtomForm();
				setState(286);
				match(RB);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ConstTermContext extends ParserRuleContext {
		public TerminalNode NAME() { return getToken(PDDLGrammarParser.NAME, 0); }
		public TerminalNode INTEGER() { return getToken(PDDLGrammarParser.INTEGER, 0); }
		public ConstTermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_constTerm; }
	}

	public final ConstTermContext constTerm() throws RecognitionException {
		ConstTermContext _localctx = new ConstTermContext(_ctx, getState());
		enterRule(_localctx, 36, RULE_constTerm);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(290);
			_la = _input.LA(1);
			if ( !(_la==NAME || _la==INTEGER) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TermContext extends ParserRuleContext {
		public TermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_term; }
	 
		public TermContext() { }
		public void copyFrom(TermContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class ModTermTermContext extends TermContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode MOD() { return getToken(PDDLGrammarParser.MOD, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public ModTermTermContext(TermContext ctx) { copyFrom(ctx); }
	}
	public static class MinusTermContext extends TermContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode MINUS() { return getToken(PDDLGrammarParser.MINUS, 0); }
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public MinusTermContext(TermContext ctx) { copyFrom(ctx); }
	}
	public static class TermMinusTermContext extends TermContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode MINUS() { return getToken(PDDLGrammarParser.MINUS, 0); }
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public TermMinusTermContext(TermContext ctx) { copyFrom(ctx); }
	}
	public static class TermModTermContext extends TermContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode MOD() { return getToken(PDDLGrammarParser.MOD, 0); }
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public TermModTermContext(TermContext ctx) { copyFrom(ctx); }
	}
	public static class BracketTermContext extends TermContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public BracketTermContext(TermContext ctx) { copyFrom(ctx); }
	}
	public static class VarContext extends TermContext {
		public TerminalNode VAR() { return getToken(PDDLGrammarParser.VAR, 0); }
		public VarContext(TermContext ctx) { copyFrom(ctx); }
	}
	public static class NameContext extends TermContext {
		public TerminalNode NAME() { return getToken(PDDLGrammarParser.NAME, 0); }
		public NameContext(TermContext ctx) { copyFrom(ctx); }
	}
	public static class PlusTermTermContext extends TermContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode PLUS() { return getToken(PDDLGrammarParser.PLUS, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public PlusTermTermContext(TermContext ctx) { copyFrom(ctx); }
	}
	public static class MinusTermTermContext extends TermContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode MINUS() { return getToken(PDDLGrammarParser.MINUS, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public MinusTermTermContext(TermContext ctx) { copyFrom(ctx); }
	}
	public static class IntegerContext extends TermContext {
		public TerminalNode INTEGER() { return getToken(PDDLGrammarParser.INTEGER, 0); }
		public IntegerContext(TermContext ctx) { copyFrom(ctx); }
	}

	public final TermContext term() throws RecognitionException {
		TermContext _localctx = new TermContext(_ctx, getState());
		enterRule(_localctx, 38, RULE_term);
		try {
			setState(334);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,19,_ctx) ) {
			case 1:
				_localctx = new NameContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(292);
				match(NAME);
				}
				break;
			case 2:
				_localctx = new VarContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(293);
				match(VAR);
				}
				break;
			case 3:
				_localctx = new IntegerContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(294);
				match(INTEGER);
				}
				break;
			case 4:
				_localctx = new BracketTermContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(295);
				match(LB);
				setState(296);
				term();
				setState(297);
				match(RB);
				}
				break;
			case 5:
				_localctx = new MinusTermContext(_localctx);
				enterOuterAlt(_localctx, 5);
				{
				setState(299);
				match(LB);
				setState(300);
				match(MINUS);
				setState(301);
				term();
				setState(302);
				match(RB);
				}
				break;
			case 6:
				_localctx = new MinusTermTermContext(_localctx);
				enterOuterAlt(_localctx, 6);
				{
				setState(304);
				match(LB);
				setState(305);
				match(MINUS);
				setState(306);
				term();
				setState(307);
				term();
				setState(308);
				match(RB);
				}
				break;
			case 7:
				_localctx = new ModTermTermContext(_localctx);
				enterOuterAlt(_localctx, 7);
				{
				setState(310);
				match(LB);
				setState(311);
				match(MOD);
				setState(312);
				term();
				setState(313);
				term();
				setState(314);
				match(RB);
				}
				break;
			case 8:
				_localctx = new TermMinusTermContext(_localctx);
				enterOuterAlt(_localctx, 8);
				{
				setState(316);
				match(LB);
				setState(317);
				term();
				setState(318);
				match(MINUS);
				setState(319);
				term();
				setState(320);
				match(RB);
				}
				break;
			case 9:
				_localctx = new TermModTermContext(_localctx);
				enterOuterAlt(_localctx, 9);
				{
				setState(322);
				match(LB);
				setState(323);
				term();
				setState(324);
				match(MOD);
				setState(325);
				term();
				setState(326);
				match(RB);
				}
				break;
			case 10:
				_localctx = new PlusTermTermContext(_localctx);
				enterOuterAlt(_localctx, 10);
				{
				setState(328);
				match(LB);
				setState(329);
				match(PLUS);
				setState(330);
				term();
				setState(331);
				term();
				setState(332);
				match(RB);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EffectContext extends ParserRuleContext {
		public EffectContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_effect; }
	 
		public EffectContext() { }
		public void copyFrom(EffectContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class AndCEffectContext extends EffectContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode AND() { return getToken(PDDLGrammarParser.AND, 0); }
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public List<CEffectContext> cEffect() {
			return getRuleContexts(CEffectContext.class);
		}
		public CEffectContext cEffect(int i) {
			return getRuleContext(CEffectContext.class,i);
		}
		public AndCEffectContext(EffectContext ctx) { copyFrom(ctx); }
	}
	public static class CeffectContext extends EffectContext {
		public CEffectContext cEffect() {
			return getRuleContext(CEffectContext.class,0);
		}
		public CeffectContext(EffectContext ctx) { copyFrom(ctx); }
	}

	public final EffectContext effect() throws RecognitionException {
		EffectContext _localctx = new EffectContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_effect);
		int _la;
		try {
			setState(346);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,21,_ctx) ) {
			case 1:
				_localctx = new AndCEffectContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(336);
				match(LB);
				setState(337);
				match(AND);
				setState(339); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(338);
					cEffect();
					}
					}
					setState(341); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==LB );
				setState(343);
				match(RB);
				}
				break;
			case 2:
				_localctx = new CeffectContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(345);
				cEffect();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class CEffectContext extends ParserRuleContext {
		public CEffectContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_cEffect; }
	 
		public CEffectContext() { }
		public void copyFrom(CEffectContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class WhenCondEffectContext extends CEffectContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode WHEN() { return getToken(PDDLGrammarParser.WHEN, 0); }
		public GdContext gd() {
			return getRuleContext(GdContext.class,0);
		}
		public CondEffectContext condEffect() {
			return getRuleContext(CondEffectContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public WhenCondEffectContext(CEffectContext ctx) { copyFrom(ctx); }
	}
	public static class CEffectPEffectContext extends CEffectContext {
		public PEffectContext pEffect() {
			return getRuleContext(PEffectContext.class,0);
		}
		public CEffectPEffectContext(CEffectContext ctx) { copyFrom(ctx); }
	}

	public final CEffectContext cEffect() throws RecognitionException {
		CEffectContext _localctx = new CEffectContext(_ctx, getState());
		enterRule(_localctx, 42, RULE_cEffect);
		try {
			setState(355);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,22,_ctx) ) {
			case 1:
				_localctx = new WhenCondEffectContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(348);
				match(LB);
				setState(349);
				match(WHEN);
				setState(350);
				gd();
				setState(351);
				condEffect();
				setState(352);
				match(RB);
				}
				break;
			case 2:
				_localctx = new CEffectPEffectContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(354);
				pEffect();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class CondEffectContext extends ParserRuleContext {
		public CondEffectContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_condEffect; }
	 
		public CondEffectContext() { }
		public void copyFrom(CondEffectContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class AndPEffectContext extends CondEffectContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode AND() { return getToken(PDDLGrammarParser.AND, 0); }
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public List<PEffectContext> pEffect() {
			return getRuleContexts(PEffectContext.class);
		}
		public PEffectContext pEffect(int i) {
			return getRuleContext(PEffectContext.class,i);
		}
		public AndPEffectContext(CondEffectContext ctx) { copyFrom(ctx); }
	}
	public static class CondEffectPEffectContext extends CondEffectContext {
		public PEffectContext pEffect() {
			return getRuleContext(PEffectContext.class,0);
		}
		public CondEffectPEffectContext(CondEffectContext ctx) { copyFrom(ctx); }
	}

	public final CondEffectContext condEffect() throws RecognitionException {
		CondEffectContext _localctx = new CondEffectContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_condEffect);
		int _la;
		try {
			setState(367);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,24,_ctx) ) {
			case 1:
				_localctx = new AndPEffectContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(357);
				match(LB);
				setState(358);
				match(AND);
				setState(360); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(359);
					pEffect();
					}
					}
					setState(362); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==LB );
				setState(364);
				match(RB);
				}
				break;
			case 2:
				_localctx = new CondEffectPEffectContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(366);
				pEffect();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class PEffectContext extends ParserRuleContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public AssignopContext assignop() {
			return getRuleContext(AssignopContext.class,0);
		}
		public TerminalNode VAR() { return getToken(PDDLGrammarParser.VAR, 0); }
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public PEffectContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_pEffect; }
	}

	public final PEffectContext pEffect() throws RecognitionException {
		PEffectContext _localctx = new PEffectContext(_ctx, getState());
		enterRule(_localctx, 46, RULE_pEffect);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(369);
			match(LB);
			setState(370);
			assignop();
			setState(371);
			match(VAR);
			setState(372);
			term();
			setState(373);
			match(RB);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssignopContext extends ParserRuleContext {
		public AssignopContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assignop; }
	 
		public AssignopContext() { }
		public void copyFrom(AssignopContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class DecContext extends AssignopContext {
		public TerminalNode DEC() { return getToken(PDDLGrammarParser.DEC, 0); }
		public DecContext(AssignopContext ctx) { copyFrom(ctx); }
	}
	public static class IncContext extends AssignopContext {
		public TerminalNode INC() { return getToken(PDDLGrammarParser.INC, 0); }
		public IncContext(AssignopContext ctx) { copyFrom(ctx); }
	}
	public static class AssignContext extends AssignopContext {
		public TerminalNode ASSIGN() { return getToken(PDDLGrammarParser.ASSIGN, 0); }
		public AssignContext(AssignopContext ctx) { copyFrom(ctx); }
	}

	public final AssignopContext assignop() throws RecognitionException {
		AssignopContext _localctx = new AssignopContext(_ctx, getState());
		enterRule(_localctx, 48, RULE_assignop);
		try {
			setState(378);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case INC:
				_localctx = new IncContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(375);
				match(INC);
				}
				break;
			case DEC:
				_localctx = new DecContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(376);
				match(DEC);
				}
				break;
			case ASSIGN:
				_localctx = new AssignContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(377);
				match(ASSIGN);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ProblemNameContext extends ParserRuleContext {
		public TerminalNode NAME() { return getToken(PDDLGrammarParser.NAME, 0); }
		public ProblemNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_problemName; }
	}

	public final ProblemNameContext problemName() throws RecognitionException {
		ProblemNameContext _localctx = new ProblemNameContext(_ctx, getState());
		enterRule(_localctx, 50, RULE_problemName);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(380);
			match(NAME);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DomainNameContext extends ParserRuleContext {
		public TerminalNode NAME() { return getToken(PDDLGrammarParser.NAME, 0); }
		public DomainNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_domainName; }
	}

	public final DomainNameContext domainName() throws RecognitionException {
		DomainNameContext _localctx = new DomainNameContext(_ctx, getState());
		enterRule(_localctx, 52, RULE_domainName);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(382);
			match(NAME);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AgentDefineContext extends ParserRuleContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode COLON() { return getToken(PDDLGrammarParser.COLON, 0); }
		public TerminalNode AGENT() { return getToken(PDDLGrammarParser.AGENT, 0); }
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public List<TerminalNode> NAME() { return getTokens(PDDLGrammarParser.NAME); }
		public TerminalNode NAME(int i) {
			return getToken(PDDLGrammarParser.NAME, i);
		}
		public AgentDefineContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_agentDefine; }
	}

	public final AgentDefineContext agentDefine() throws RecognitionException {
		AgentDefineContext _localctx = new AgentDefineContext(_ctx, getState());
		enterRule(_localctx, 54, RULE_agentDefine);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(384);
			match(LB);
			setState(385);
			match(COLON);
			setState(386);
			match(AGENT);
			setState(388); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(387);
				match(NAME);
				}
				}
				setState(390); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==NAME );
			setState(392);
			match(RB);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ObjectDeclarationContext extends ParserRuleContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode COLON() { return getToken(PDDLGrammarParser.COLON, 0); }
		public TerminalNode OBJS() { return getToken(PDDLGrammarParser.OBJS, 0); }
		public ListNameContext listName() {
			return getRuleContext(ListNameContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public ObjectDeclarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_objectDeclaration; }
	}

	public final ObjectDeclarationContext objectDeclaration() throws RecognitionException {
		ObjectDeclarationContext _localctx = new ObjectDeclarationContext(_ctx, getState());
		enterRule(_localctx, 56, RULE_objectDeclaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(394);
			match(LB);
			setState(395);
			match(COLON);
			setState(396);
			match(OBJS);
			setState(397);
			listName();
			setState(398);
			match(RB);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class InitContext extends ParserRuleContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public TerminalNode COLON() { return getToken(PDDLGrammarParser.COLON, 0); }
		public TerminalNode INIT() { return getToken(PDDLGrammarParser.INIT, 0); }
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public List<ConstTermAtomFormContext> constTermAtomForm() {
			return getRuleContexts(ConstTermAtomFormContext.class);
		}
		public ConstTermAtomFormContext constTermAtomForm(int i) {
			return getRuleContext(ConstTermAtomFormContext.class,i);
		}
		public InitContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_init; }
	}

	public final InitContext init() throws RecognitionException {
		InitContext _localctx = new InitContext(_ctx, getState());
		enterRule(_localctx, 58, RULE_init);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(400);
			match(LB);
			setState(401);
			match(COLON);
			setState(402);
			match(INIT);
			setState(406);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==LB) {
				{
				{
				setState(403);
				constTermAtomForm();
				}
				}
				setState(408);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(409);
			match(RB);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ConstTermAtomFormContext extends ParserRuleContext {
		public TerminalNode LB() { return getToken(PDDLGrammarParser.LB, 0); }
		public PredicateContext predicate() {
			return getRuleContext(PredicateContext.class,0);
		}
		public TerminalNode RB() { return getToken(PDDLGrammarParser.RB, 0); }
		public List<ConstTermContext> constTerm() {
			return getRuleContexts(ConstTermContext.class);
		}
		public ConstTermContext constTerm(int i) {
			return getRuleContext(ConstTermContext.class,i);
		}
		public TerminalNode EQ() { return getToken(PDDLGrammarParser.EQ, 0); }
		public TerminalNode LT() { return getToken(PDDLGrammarParser.LT, 0); }
		public TerminalNode LEQ() { return getToken(PDDLGrammarParser.LEQ, 0); }
		public TerminalNode GT() { return getToken(PDDLGrammarParser.GT, 0); }
		public TerminalNode GEQ() { return getToken(PDDLGrammarParser.GEQ, 0); }
		public ConstTermAtomFormContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_constTermAtomForm; }
	}

	public final ConstTermAtomFormContext constTermAtomForm() throws RecognitionException {
		ConstTermAtomFormContext _localctx = new ConstTermAtomFormContext(_ctx, getState());
		enterRule(_localctx, 60, RULE_constTermAtomForm);
		int _la;
		try {
			setState(451);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,29,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(411);
				match(LB);
				setState(412);
				predicate();
				setState(416);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==NAME || _la==INTEGER) {
					{
					{
					setState(413);
					constTerm();
					}
					}
					setState(418);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(419);
				match(RB);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(421);
				match(LB);
				setState(422);
				match(EQ);
				setState(423);
				constTerm();
				setState(424);
				constTerm();
				setState(425);
				match(RB);
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(427);
				match(LB);
				setState(428);
				match(LT);
				setState(429);
				constTerm();
				setState(430);
				constTerm();
				setState(431);
				match(RB);
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(433);
				match(LB);
				setState(434);
				match(LEQ);
				setState(435);
				constTerm();
				setState(436);
				constTerm();
				setState(437);
				match(RB);
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(439);
				match(LB);
				setState(440);
				match(GT);
				setState(441);
				constTerm();
				setState(442);
				constTerm();
				setState(443);
				match(RB);
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(445);
				match(LB);
				setState(446);
				match(GEQ);
				setState(447);
				constTerm();
				setState(448);
				constTerm();
				setState(449);
				match(RB);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3C\u01c8\4\2\t\2\4"+
		"\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t"+
		"\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \3\2"+
		"\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\7\2L\n\2\f\2\16\2O\13\2\3\2\3"+
		"\2\3\3\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4\3\4\3\4\3\5\3\5\3\5\3\5\3\5"+
		"\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\7\3\7\3\b\3\b\3\t\3\t\3\t\3\t\3\t\3\t\3"+
		"\t\3\t\3\t\3\t\5\ty\n\t\3\t\3\t\3\t\5\t~\n\t\3\t\3\t\3\t\5\t\u0083\n\t"+
		"\3\t\3\t\3\n\3\n\3\13\3\13\3\f\3\f\3\f\5\f\u008e\n\f\3\r\3\r\3\r\5\r\u0093"+
		"\n\r\3\16\7\16\u0096\n\16\f\16\16\16\u0099\13\16\3\16\6\16\u009c\n\16"+
		"\r\16\16\16\u009d\3\16\3\16\3\16\3\16\5\16\u00a4\n\16\3\17\7\17\u00a7"+
		"\n\17\f\17\16\17\u00aa\13\17\3\17\6\17\u00ad\n\17\r\17\16\17\u00ae\3\17"+
		"\3\17\3\17\3\17\5\17\u00b5\n\17\3\20\3\20\6\20\u00b9\n\20\r\20\16\20\u00ba"+
		"\3\21\3\21\3\21\3\21\6\21\u00c1\n\21\r\21\16\21\u00c2\3\21\3\21\3\21\3"+
		"\21\3\21\6\21\u00ca\n\21\r\21\16\21\u00cb\3\21\3\21\3\21\3\21\3\21\3\21"+
		"\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21"+
		"\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\5\21\u00eb\n\21\3\22\3\22"+
		"\3\22\7\22\u00f0\n\22\f\22\16\22\u00f3\13\22\3\22\3\22\3\22\3\22\3\22"+
		"\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22"+
		"\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22"+
		"\3\22\3\22\3\22\3\22\3\22\5\22\u011b\n\22\3\23\3\23\3\23\3\23\3\23\3\23"+
		"\5\23\u0123\n\23\3\24\3\24\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25"+
		"\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25"+
		"\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25"+
		"\3\25\3\25\3\25\3\25\3\25\5\25\u0151\n\25\3\26\3\26\3\26\6\26\u0156\n"+
		"\26\r\26\16\26\u0157\3\26\3\26\3\26\5\26\u015d\n\26\3\27\3\27\3\27\3\27"+
		"\3\27\3\27\3\27\5\27\u0166\n\27\3\30\3\30\3\30\6\30\u016b\n\30\r\30\16"+
		"\30\u016c\3\30\3\30\3\30\5\30\u0172\n\30\3\31\3\31\3\31\3\31\3\31\3\31"+
		"\3\32\3\32\3\32\5\32\u017d\n\32\3\33\3\33\3\34\3\34\3\35\3\35\3\35\3\35"+
		"\6\35\u0187\n\35\r\35\16\35\u0188\3\35\3\35\3\36\3\36\3\36\3\36\3\36\3"+
		"\36\3\37\3\37\3\37\3\37\7\37\u0197\n\37\f\37\16\37\u019a\13\37\3\37\3"+
		"\37\3 \3 \3 \7 \u01a1\n \f \16 \u01a4\13 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3"+
		" \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \3 \5"+
		" \u01c6\n \3 \2\2!\2\4\6\b\n\f\16\20\22\24\26\30\32\34\36 \"$&(*,.\60"+
		"\62\64\668:<>\2\4\5\2\33\33\37\37??\3\2?@\2\u01dd\2@\3\2\2\2\4R\3\2\2"+
		"\2\6X\3\2\2\2\b^\3\2\2\2\nd\3\2\2\2\fj\3\2\2\2\16l\3\2\2\2\20n\3\2\2\2"+
		"\22\u0086\3\2\2\2\24\u0088\3\2\2\2\26\u008d\3\2\2\2\30\u0092\3\2\2\2\32"+
		"\u00a3\3\2\2\2\34\u00b4\3\2\2\2\36\u00b6\3\2\2\2 \u00ea\3\2\2\2\"\u011a"+
		"\3\2\2\2$\u0122\3\2\2\2&\u0124\3\2\2\2(\u0150\3\2\2\2*\u015c\3\2\2\2,"+
		"\u0165\3\2\2\2.\u0171\3\2\2\2\60\u0173\3\2\2\2\62\u017c\3\2\2\2\64\u017e"+
		"\3\2\2\2\66\u0180\3\2\2\28\u0182\3\2\2\2:\u018c\3\2\2\2<\u0192\3\2\2\2"+
		">\u01c5\3\2\2\2@A\7$\2\2AB\7\5\2\2BC\7$\2\2CD\7\3\2\2DE\7?\2\2EF\7%\2"+
		"\2FG\5\4\3\2GH\5\6\4\2HI\5\b\5\2IM\5\n\6\2JL\5\20\t\2KJ\3\2\2\2LO\3\2"+
		"\2\2MK\3\2\2\2MN\3\2\2\2NP\3\2\2\2OM\3\2\2\2PQ\7%\2\2Q\3\3\2\2\2RS\7$"+
		"\2\2ST\7(\2\2TU\7!\2\2UV\5\34\17\2VW\7%\2\2W\5\3\2\2\2XY\7$\2\2YZ\7(\2"+
		"\2Z[\7\b\2\2[\\\5\24\13\2\\]\7%\2\2]\7\3\2\2\2^_\7$\2\2_`\7(\2\2`a\7\20"+
		"\2\2ab\5\26\f\2bc\7%\2\2c\t\3\2\2\2de\7$\2\2ef\7(\2\2fg\7\22\2\2gh\5\26"+
		"\f\2hi\7%\2\2i\13\3\2\2\2jk\7?\2\2k\r\3\2\2\2lm\t\2\2\2m\17\3\2\2\2no"+
		"\7$\2\2op\7(\2\2pq\7\n\2\2qx\5\22\n\2rs\7(\2\2st\7\17\2\2tu\7$\2\2uv\5"+
		"\34\17\2vw\7%\2\2wy\3\2\2\2xr\3\2\2\2xy\3\2\2\2y}\3\2\2\2z{\7(\2\2{|\7"+
		"\21\2\2|~\5\26\f\2}z\3\2\2\2}~\3\2\2\2~\u0082\3\2\2\2\177\u0080\7(\2\2"+
		"\u0080\u0081\7\32\2\2\u0081\u0083\5\30\r\2\u0082\177\3\2\2\2\u0082\u0083"+
		"\3\2\2\2\u0083\u0084\3\2\2\2\u0084\u0085\7%\2\2\u0085\21\3\2\2\2\u0086"+
		"\u0087\7?\2\2\u0087\23\3\2\2\2\u0088\u0089\7?\2\2\u0089\25\3\2\2\2\u008a"+
		"\u008e\5 \21\2\u008b\u008c\7$\2\2\u008c\u008e\7%\2\2\u008d\u008a\3\2\2"+
		"\2\u008d\u008b\3\2\2\2\u008e\27\3\2\2\2\u008f\u0093\5*\26\2\u0090\u0091"+
		"\7$\2\2\u0091\u0093\7%\2\2\u0092\u008f\3\2\2\2\u0092\u0090\3\2\2\2\u0093"+
		"\31\3\2\2\2\u0094\u0096\7?\2\2\u0095\u0094\3\2\2\2\u0096\u0099\3\2\2\2"+
		"\u0097\u0095\3\2\2\2\u0097\u0098\3\2\2\2\u0098\u00a4\3\2\2\2\u0099\u0097"+
		"\3\2\2\2\u009a\u009c\7?\2\2\u009b\u009a\3\2\2\2\u009c\u009d\3\2\2\2\u009d"+
		"\u009b\3\2\2\2\u009d\u009e\3\2\2\2\u009e\u009f\3\2\2\2\u009f\u00a0\7,"+
		"\2\2\u00a0\u00a1\5\16\b\2\u00a1\u00a2\5\32\16\2\u00a2\u00a4\3\2\2\2\u00a3"+
		"\u0097\3\2\2\2\u00a3\u009b\3\2\2\2\u00a4\33\3\2\2\2\u00a5\u00a7\7A\2\2"+
		"\u00a6\u00a5\3\2\2\2\u00a7\u00aa\3\2\2\2\u00a8\u00a6\3\2\2\2\u00a8\u00a9"+
		"\3\2\2\2\u00a9\u00b5\3\2\2\2\u00aa\u00a8\3\2\2\2\u00ab\u00ad\7A\2\2\u00ac"+
		"\u00ab\3\2\2\2\u00ad\u00ae\3\2\2\2\u00ae\u00ac\3\2\2\2\u00ae\u00af\3\2"+
		"\2\2\u00af\u00b0\3\2\2\2\u00b0\u00b1\7,\2\2\u00b1\u00b2\5\16\b\2\u00b2"+
		"\u00b3\5\34\17\2\u00b3\u00b5\3\2\2\2\u00b4\u00a8\3\2\2\2\u00b4\u00ac\3"+
		"\2\2\2\u00b5\35\3\2\2\2\u00b6\u00b8\7:\2\2\u00b7\u00b9\7A\2\2\u00b8\u00b7"+
		"\3\2\2\2\u00b9\u00ba\3\2\2\2\u00ba\u00b8\3\2\2\2\u00ba\u00bb\3\2\2\2\u00bb"+
		"\37\3\2\2\2\u00bc\u00eb\5\"\22\2\u00bd\u00be\7$\2\2\u00be\u00c0\7\67\2"+
		"\2\u00bf\u00c1\5 \21\2\u00c0\u00bf\3\2\2\2\u00c1\u00c2\3\2\2\2\u00c2\u00c0"+
		"\3\2\2\2\u00c2\u00c3\3\2\2\2\u00c3\u00c4\3\2\2\2\u00c4\u00c5\7%\2\2\u00c5"+
		"\u00eb\3\2\2\2\u00c6\u00c7\7$\2\2\u00c7\u00c9\78\2\2\u00c8\u00ca\5 \21"+
		"\2\u00c9\u00c8\3\2\2\2\u00ca\u00cb\3\2\2\2\u00cb\u00c9\3\2\2\2\u00cb\u00cc"+
		"\3\2\2\2\u00cc\u00cd\3\2\2\2\u00cd\u00ce\7%\2\2\u00ce\u00eb\3\2\2\2\u00cf"+
		"\u00d0\7$\2\2\u00d0\u00d1\79\2\2\u00d1\u00d2\5 \21\2\u00d2\u00d3\7%\2"+
		"\2\u00d3\u00eb\3\2\2\2\u00d4\u00d5\7$\2\2\u00d5\u00d6\7;\2\2\u00d6\u00d7"+
		"\5 \21\2\u00d7\u00d8\5 \21\2\u00d8\u00d9\7%\2\2\u00d9\u00eb\3\2\2\2\u00da"+
		"\u00db\7$\2\2\u00db\u00dc\7=\2\2\u00dc\u00dd\7$\2\2\u00dd\u00de\5\34\17"+
		"\2\u00de\u00df\7%\2\2\u00df\u00e0\5 \21\2\u00e0\u00e1\7%\2\2\u00e1\u00eb"+
		"\3\2\2\2\u00e2\u00e3\7$\2\2\u00e3\u00e4\7<\2\2\u00e4\u00e5\7$\2\2\u00e5"+
		"\u00e6\5\34\17\2\u00e6\u00e7\7%\2\2\u00e7\u00e8\5 \21\2\u00e8\u00e9\7"+
		"%\2\2\u00e9\u00eb\3\2\2\2\u00ea\u00bc\3\2\2\2\u00ea\u00bd\3\2\2\2\u00ea"+
		"\u00c6\3\2\2\2\u00ea\u00cf\3\2\2\2\u00ea\u00d4\3\2\2\2\u00ea\u00da\3\2"+
		"\2\2\u00ea\u00e2\3\2\2\2\u00eb!\3\2\2\2\u00ec\u00ed\7$\2\2\u00ed\u00f1"+
		"\5\f\7\2\u00ee\u00f0\5(\25\2\u00ef\u00ee\3\2\2\2\u00f0\u00f3\3\2\2\2\u00f1"+
		"\u00ef\3\2\2\2\u00f1\u00f2\3\2\2\2\u00f2\u00f4\3\2\2\2\u00f3\u00f1\3\2"+
		"\2\2\u00f4\u00f5\7%\2\2\u00f5\u011b\3\2\2\2\u00f6\u00f7\7$\2\2\u00f7\u00f8"+
		"\7\61\2\2\u00f8\u00f9\5(\25\2\u00f9\u00fa\5(\25\2\u00fa\u00fb\7%\2\2\u00fb"+
		"\u011b\3\2\2\2\u00fc\u00fd\7$\2\2\u00fd\u00fe\7\62\2\2\u00fe\u00ff\5("+
		"\25\2\u00ff\u0100\5(\25\2\u0100\u0101\7%\2\2\u0101\u011b\3\2\2\2\u0102"+
		"\u0103\7$\2\2\u0103\u0104\7\63\2\2\u0104\u0105\5(\25\2\u0105\u0106\5("+
		"\25\2\u0106\u0107\7%\2\2\u0107\u011b\3\2\2\2\u0108\u0109\7$\2\2\u0109"+
		"\u010a\7\64\2\2\u010a\u010b\5(\25\2\u010b\u010c\5(\25\2\u010c\u010d\7"+
		"%\2\2\u010d\u011b\3\2\2\2\u010e\u010f\7$\2\2\u010f\u0110\7\65\2\2\u0110"+
		"\u0111\5(\25\2\u0111\u0112\5(\25\2\u0112\u0113\7%\2\2\u0113\u011b\3\2"+
		"\2\2\u0114\u0115\7$\2\2\u0115\u0116\7\66\2\2\u0116\u0117\5(\25\2\u0117"+
		"\u0118\5(\25\2\u0118\u0119\7%\2\2\u0119\u011b\3\2\2\2\u011a\u00ec\3\2"+
		"\2\2\u011a\u00f6\3\2\2\2\u011a\u00fc\3\2\2\2\u011a\u0102\3\2\2\2\u011a"+
		"\u0108\3\2\2\2\u011a\u010e\3\2\2\2\u011a\u0114\3\2\2\2\u011b#\3\2\2\2"+
		"\u011c\u0123\5\"\22\2\u011d\u011e\7$\2\2\u011e\u011f\79\2\2\u011f\u0120"+
		"\5\"\22\2\u0120\u0121\7%\2\2\u0121\u0123\3\2\2\2\u0122\u011c\3\2\2\2\u0122"+
		"\u011d\3\2\2\2\u0123%\3\2\2\2\u0124\u0125\t\3\2\2\u0125\'\3\2\2\2\u0126"+
		"\u0151\7?\2\2\u0127\u0151\7A\2\2\u0128\u0151\7@\2\2\u0129\u012a\7$\2\2"+
		"\u012a\u012b\5(\25\2\u012b\u012c\7%\2\2\u012c\u0151\3\2\2\2\u012d\u012e"+
		"\7$\2\2\u012e\u012f\7,\2\2\u012f\u0130\5(\25\2\u0130\u0131\7%\2\2\u0131"+
		"\u0151\3\2\2\2\u0132\u0133\7$\2\2\u0133\u0134\7,\2\2\u0134\u0135\5(\25"+
		"\2\u0135\u0136\5(\25\2\u0136\u0137\7%\2\2\u0137\u0151\3\2\2\2\u0138\u0139"+
		"\7$\2\2\u0139\u013a\7\60\2\2\u013a\u013b\5(\25\2\u013b\u013c\5(\25\2\u013c"+
		"\u013d\7%\2\2\u013d\u0151\3\2\2\2\u013e\u013f\7$\2\2\u013f\u0140\5(\25"+
		"\2\u0140\u0141\7,\2\2\u0141\u0142\5(\25\2\u0142\u0143\7%\2\2\u0143\u0151"+
		"\3\2\2\2\u0144\u0145\7$\2\2\u0145\u0146\5(\25\2\u0146\u0147\7\60\2\2\u0147"+
		"\u0148\5(\25\2\u0148\u0149\7%\2\2\u0149\u0151\3\2\2\2\u014a\u014b\7$\2"+
		"\2\u014b\u014c\7-\2\2\u014c\u014d\5(\25\2\u014d\u014e\5(\25\2\u014e\u014f"+
		"\7%\2\2\u014f\u0151\3\2\2\2\u0150\u0126\3\2\2\2\u0150\u0127\3\2\2\2\u0150"+
		"\u0128\3\2\2\2\u0150\u0129\3\2\2\2\u0150\u012d\3\2\2\2\u0150\u0132\3\2"+
		"\2\2\u0150\u0138\3\2\2\2\u0150\u013e\3\2\2\2\u0150\u0144\3\2\2\2\u0150"+
		"\u014a\3\2\2\2\u0151)\3\2\2\2\u0152\u0153\7$\2\2\u0153\u0155\7\67\2\2"+
		"\u0154\u0156\5,\27\2\u0155\u0154\3\2\2\2\u0156\u0157\3\2\2\2\u0157\u0155"+
		"\3\2\2\2\u0157\u0158\3\2\2\2\u0158\u0159\3\2\2\2\u0159\u015a\7%\2\2\u015a"+
		"\u015d\3\2\2\2\u015b\u015d\5,\27\2\u015c\u0152\3\2\2\2\u015c\u015b\3\2"+
		"\2\2\u015d+\3\2\2\2\u015e\u015f\7$\2\2\u015f\u0160\7>\2\2\u0160\u0161"+
		"\5 \21\2\u0161\u0162\5.\30\2\u0162\u0163\7%\2\2\u0163\u0166\3\2\2\2\u0164"+
		"\u0166\5\60\31\2\u0165\u015e\3\2\2\2\u0165\u0164\3\2\2\2\u0166-\3\2\2"+
		"\2\u0167\u0168\7$\2\2\u0168\u016a\7\67\2\2\u0169\u016b\5\60\31\2\u016a"+
		"\u0169\3\2\2\2\u016b\u016c\3\2\2\2\u016c\u016a\3\2\2\2\u016c\u016d\3\2"+
		"\2\2\u016d\u016e\3\2\2\2\u016e\u016f\7%\2\2\u016f\u0172\3\2\2\2\u0170"+
		"\u0172\5\60\31\2\u0171\u0167\3\2\2\2\u0171\u0170\3\2\2\2\u0172/\3\2\2"+
		"\2\u0173\u0174\7$\2\2\u0174\u0175\5\62\32\2\u0175\u0176\7A\2\2\u0176\u0177"+
		"\5(\25\2\u0177\u0178\7%\2\2\u0178\61\3\2\2\2\u0179\u017d\7\34\2\2\u017a"+
		"\u017d\7\35\2\2\u017b\u017d\7\36\2\2\u017c\u0179\3\2\2\2\u017c\u017a\3"+
		"\2\2\2\u017c\u017b\3\2\2\2\u017d\63\3\2\2\2\u017e\u017f\7?\2\2\u017f\65"+
		"\3\2\2\2\u0180\u0181\7?\2\2\u0181\67\3\2\2\2\u0182\u0183\7$\2\2\u0183"+
		"\u0184\7(\2\2\u0184\u0186\7\37\2\2\u0185\u0187\7?\2\2\u0186\u0185\3\2"+
		"\2\2\u0187\u0188\3\2\2\2\u0188\u0186\3\2\2\2\u0188\u0189\3\2\2\2\u0189"+
		"\u018a\3\2\2\2\u018a\u018b\7%\2\2\u018b9\3\2\2\2\u018c\u018d\7$\2\2\u018d"+
		"\u018e\7(\2\2\u018e\u018f\7!\2\2\u018f\u0190\5\32\16\2\u0190\u0191\7%"+
		"\2\2\u0191;\3\2\2\2\u0192\u0193\7$\2\2\u0193\u0194\7(\2\2\u0194\u0198"+
		"\7\"\2\2\u0195\u0197\5> \2\u0196\u0195\3\2\2\2\u0197\u019a\3\2\2\2\u0198"+
		"\u0196\3\2\2\2\u0198\u0199\3\2\2\2\u0199\u019b\3\2\2\2\u019a\u0198\3\2"+
		"\2\2\u019b\u019c\7%\2\2\u019c=\3\2\2\2\u019d\u019e\7$\2\2\u019e\u01a2"+
		"\5\f\7\2\u019f\u01a1\5&\24\2\u01a0\u019f\3\2\2\2\u01a1\u01a4\3\2\2\2\u01a2"+
		"\u01a0\3\2\2\2\u01a2\u01a3\3\2\2\2\u01a3\u01a5\3\2\2\2\u01a4\u01a2\3\2"+
		"\2\2\u01a5\u01a6\7%\2\2\u01a6\u01c6\3\2\2\2\u01a7\u01a8\7$\2\2\u01a8\u01a9"+
		"\7\61\2\2\u01a9\u01aa\5&\24\2\u01aa\u01ab\5&\24\2\u01ab\u01ac\7%\2\2\u01ac"+
		"\u01c6\3\2\2\2\u01ad\u01ae\7$\2\2\u01ae\u01af\7\63\2\2\u01af\u01b0\5&"+
		"\24\2\u01b0\u01b1\5&\24\2\u01b1\u01b2\7%\2\2\u01b2\u01c6\3\2\2\2\u01b3"+
		"\u01b4\7$\2\2\u01b4\u01b5\7\64\2\2\u01b5\u01b6\5&\24\2\u01b6\u01b7\5&"+
		"\24\2\u01b7\u01b8\7%\2\2\u01b8\u01c6\3\2\2\2\u01b9\u01ba\7$\2\2\u01ba"+
		"\u01bb\7\65\2\2\u01bb\u01bc\5&\24\2\u01bc\u01bd\5&\24\2\u01bd\u01be\7"+
		"%\2\2\u01be\u01c6\3\2\2\2\u01bf\u01c0\7$\2\2\u01c0\u01c1\7\66\2\2\u01c1"+
		"\u01c2\5&\24\2\u01c2\u01c3\5&\24\2\u01c3\u01c4\7%\2\2\u01c4\u01c6\3\2"+
		"\2\2\u01c5\u019d\3\2\2\2\u01c5\u01a7\3\2\2\2\u01c5\u01ad\3\2\2\2\u01c5"+
		"\u01b3\3\2\2\2\u01c5\u01b9\3\2\2\2\u01c5\u01bf\3\2\2\2\u01c6?\3\2\2\2"+
		" Mx}\u0082\u008d\u0092\u0097\u009d\u00a3\u00a8\u00ae\u00b4\u00ba\u00c2"+
		"\u00cb\u00ea\u00f1\u011a\u0122\u0150\u0157\u015c\u0165\u016c\u0171\u017c"+
		"\u0188\u0198\u01a2\u01c5";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}