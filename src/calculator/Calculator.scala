package calculator

import java.awt.BorderLayout
import java.awt.event.ActionEvent
import java.text.ParseException
import java.util.Stack
import scala.collection.mutable.ListBuffer
import javax.swing.JFrame
import javax.swing.JTextField
import java.awt.event.ActionListener
import java.awt.Dimension
import javax.swing.JScrollPane
import javax.swing.JTextArea

/**
 * Supported operator types.
 */
object OperatorType extends Enumeration 
{
  val PLUS = Value("+")
  val MINUS = Value("-")  
  val MULTIPLY = Value("*")
  val DIVIDE = Value("/")
  val PARENS = Value("(")
}

/**
 * Text scanner.
 */
trait IScanner {
  def eof() : Boolean
  def peek() : Char
  def next() : Char
  def offset : Int
  def setOffset(offset:Int)
}

/**
 * A parsed input text token.
 */
sealed case class Token(val tokenType:TokenType.Value,val offset:Int,val text:String)

/**
 * Recognized token types.
 */
object TokenType extends Enumeration 
{
  val NUMBER_LITERAL = Value("NUMBER_LITERAL")
  val PLUS = Value("PLUS")
  val MINUS = Value("MINUS")  
  val MULTIPLY = Value("MULTIPLY")
  val DIVIDE = Value("DIVIDE")
  val PARENS_OPEN = Value("(")
  val PARENS_CLOSE = Value(")")
}

/**
 * Abstract syntax tree (AST) node.
 */
abstract class ASTNode 
{
  val children = ListBuffer[ASTNode]()
  
  /**
   * Returns the maximum number of childs this node may have.
   * 
   * Trying to add more children via {@link #addChild(ASTNode)} will throw an 
   * <code>UnsupportedOperationException</code>.
   * @return max. number of supported child nodes 
   */
  def maxChildCount : Int
    
  /**
   * Adds a new child node.
   * 
   * @see #maxChildCound()
   * @throws UnsupportedOperationException If trying to add a node although <code>maxChildCount</code> has already been reached 
   */
  final def addChild(child:ASTNode)
  {
    if ( (children.size+1) > maxChildCount ) {
      throw new UnsupportedOperationException("Node "+this.getClass+" supports at most "+maxChildCount+" child nodes, cannot add "+child+" to "+this)
    }
    children += child
  }

  final def visit(visitor: (ASTNode,Int) => Unit ) : Unit =  visit(visitor,0)
  
  private final def visit(visitor: (ASTNode,Int) => Unit,depth:Int) {
    visitor( this , depth )    
    children.foreach( _.visit( visitor , depth+1 ) )
  }
  
  /**
   * DEBUG: Returns an ASCII representation of this subtree.
   * @return ASCII art
   */
  def print() : String = {
    val builder = new StringBuffer
    visit( (node,depth) => builder.append( "\n"+"-"*depth+" => "+node.toString ) )
    builder.toString
  }
  
  /**
   * Evaluates this subtree.
   * 
   * @return Evaluation result
   */
  def evaluate() : Int
}

/**
 * Tokenizes the input text returned by a scanner.
 */
trait ILexer 
{  
  /**
   * Check for EOF.
   * 
   * @return <code>true</code> if the end of the input text has been reached and
   * no more tokens are avilable.  
   */
  def eof() : Boolean
  
  /**
   * Peeks at the current input token without actually removing
   * it from the input.
   * @throws ParseException if the lexer is already at EOF 
   */
  def peek() : Token
  
  /**
   * Checks the type of the current token.
   * @param expected Expected token type
   * @return <code>true</code> if this lexer is not at EOF and the current
   * token has the given type
   */
  def peek(expected : TokenType.Value ) : Boolean  
  
  /**
   * Returns the next token from the input text.
   * @return next token
   * @throws ParseException if the lexer is already at EOF    
   */
  def next() : Token  
  
  /**
   * Returns the next token from the input text,assuring that
   * the token has a specific type.
   * @param expected
   * @return next token
   * @throws ParseException if the lexer is already at EOF or the token
   * does not have the expected type    
   */  
  def next(expected : TokenType.Value ) : Token
  
  /**
   * Returns the lexer's current parse offset.
   * @return parse offset
   */
  def offset : Int  
  
  /**
   * Remembers the lexer's current state on an internal state stack.
   * @see #recallState()
   * @see #discardState()
   */
  def rememberState()
  
  /**
   * Restores the lexer's state from the internal state stack.
   * 
   * @throws IllegalStateException if no state is on the internal state stack
   */
  def recallState()
  
  /**
   * Discards the last remembered state from the lexer's internal state stack.
   */
  def discardState()
}

final class Scanner(val input:String) extends IScanner 
{
  private var index = 0
  
  override def eof() : Boolean = index >= input.length()
  
  override def offset : Int = index
  
  override def setOffset(offset:Int) : Unit = index=offset
  
  private def getChar(index:Int,increment:Int=0):Char= {
    if ( index >= input.length() ) {
      throw new IllegalStateException("At EOF")
    }
    this.index += increment
    input.charAt(index)    
  }
  
  override def peek() : Char = getChar(index)
  
  override def next() : Char = getChar(index,1)
}

final class Lexer(val input:IScanner) extends ILexer {

  private val NUMBER_PATTERN = "([0-9]+)".r  
  
  private val tokens = ListBuffer[Token]()  
  private val buffer = new StringBuilder()
  private val stack = new scala.collection.mutable.Stack[LexerState]()
  
  protected final class LexerState 
  {  
    private val oldTokens = tokens.toList
    private val scannerOffset = input.offset
    
    def recallState() {
      input.setOffset( scannerOffset )
      tokens.clear()
      tokens ++ oldTokens
    }
  }
  
  override def rememberState() : Unit = stack.push( new LexerState )
  
  override def discardState() : Unit = stack.pop()
  
  override def recallState() : Unit = stack.pop().recallState()

  override def offset() : Int = if ( eof() ) input.offset else tokens(0).offset
  
  override def eof() : Boolean = {
    if ( tokens.isEmpty ) {
    	parseTokens()
    }
    return tokens.isEmpty
  }
  
  private def parseTokens() 
  {    
    buffer.setLength(0)
    
    while ( ! input.eof && input.peek().isWhitespace ) {}
    
    val currentOffset = input.offset
    while ( ! input.eof && ! input.peek().isWhitespace ) 
    {
      val currentChar = input.next()
      toTokenType( currentChar ) match 
      {
        case Some(_@tokenType) => {
          processBuffer(currentOffset);    	       
          queueToken( tokenType , currentOffset+buffer.length , currentChar.toString )
          return          
        }
        case None => buffer.append( currentChar )
      }
     }
     processBuffer(currentOffset);
  }
  
  private def toTokenType(c:Char) : Option[TokenType.Value] = c match {
    case '(' => Some(TokenType.PARENS_OPEN)
    case ')' => Some(TokenType.PARENS_CLOSE)
    case '+' => Some(TokenType.PLUS)
    case '-' => Some(TokenType.MINUS)
    case '*' => Some(TokenType.MULTIPLY)
    case '/' => Some(TokenType.DIVIDE) 
    case _   => None
  }
  
  private def queueToken(tokenType : TokenType.Value, offset:Int,value : String ) : Unit =  tokens += Token(tokenType,offset,value)
  
  private def processBuffer(offset:Int) {    
    buffer.toString match 
    {
      case "" =>
      case NUMBER_PATTERN(c) => queueToken( TokenType.NUMBER_LITERAL , offset,c )
      case _ => throw new RuntimeException("Internal error,unparsable buffer: >"+buffer+"<")
    } 
  }
  
  private def assertNotEOF() : Unit = if ( eof() )  throw new ParseException("Uexpected EOF", input.offset )
  
  override def peek() : Token = {
    assertNotEOF()
    tokens(0)
  }
  
  override def peek(tt : TokenType.Value ) : Boolean = ! eof() && tokens(0).tokenType == tt;
  
  override def next(): Token = 
  {
    assertNotEOF()
    tokens.remove(0)
  }   
  
  override def next(expected:TokenType.Value): Token = 
  {
    if ( eof() ) {
      throw new ParseException("Unexpected EOF while looking for "+expected,input.offset );
    }
    if ( peek().tokenType != expected ) {
      throw new ParseException("Unexpected token "+peek()+",expected: "+expected,peek().offset );
    }
     tokens.remove(0)
  }     
}

final class AST extends ASTNode 
{
  override def toString() : String = "AST"
  
  override def evaluate() : Int = if ( ! children.isEmpty ) children(0).evaluate() else 0
  
  override val maxChildCount : Int = 1
}

final class NumberNode(val value:Int) extends ASTNode 
{
  def this(token:Token) = this( token.text.toInt )
  
  override val maxChildCount : Int = 0
  
  override def evaluate() : Int = value
  
  override def toString() : String = value.toString
}

final class OperatorNode(val opType:OperatorType.Value) extends ASTNode 
{
  override val maxChildCount : Int = 2  
  
  def this(token:Token) 
  {
    this( token.tokenType match {
      case TokenType.PARENS_OPEN => OperatorType.PARENS      
      case TokenType.MULTIPLY => OperatorType.MULTIPLY
      case TokenType.PLUS => OperatorType.PLUS
      case TokenType.MINUS => OperatorType.MINUS
      case TokenType.DIVIDE => OperatorType.DIVIDE      
      case _ => throw new RuntimeException("Unhandled token: "+token);
    })    
  }
  
  override def evaluate() : Int = opType match {
      case OperatorType.PARENS => children(0).evaluate()    
      case OperatorType.PLUS => children(0).evaluate() + children(1).evaluate
      case OperatorType.MULTIPLY => children(0).evaluate() * children(1).evaluate
      case OperatorType.DIVIDE => children(0).evaluate() / children(1).evaluate
      case OperatorType.MINUS => children(0).evaluate() - children(1).evaluate      
      case _ => throw new RuntimeException("Unhandled operator "+opType)
  }
  
  override def toString() : String = opType match 
  {
    case OperatorType.PLUS => "+("+seqToString( children )+")"
    case OperatorType.MULTIPLY => "*("+seqToString( children) +")"
    case OperatorType.MINUS => "-("+seqToString( children )+")"
    case OperatorType.DIVIDE => "/("+seqToString( children) +")"    
    case OperatorType.PARENS => "PARENS("+seqToString( children) +")"        
    case _ => "Unhandled operator type "+opType
  }
  
  protected final def seqToString[A](seq:Seq[A] ) : String =  seq.foldRight("")( (string,node) => string+","+node.toString )
}

/**
 * Parser for algebraic expressions.
 *  
 * <expr>   :=  <term> ( '+' | '-' ) <expr>  |   <term>            
 * <term>      :=  <factor> ( '*' | '/' ) <term> |   <factor>                
 * <factor>    :=  \d+ | '(' <expr> ')'
 */
class ExpressionParser(input:String)
{
  private val scanner : IScanner = new Scanner(input)
  private val lexer : ILexer = new Lexer(scanner)

  private val current = new Stack[ASTNode]
  
  def parse() : AST = 
  {
    while ( ! lexer.eof ) 
    {
	  if ( ! expression() ) 
	  {
		  throw new ParseException("Syntax error",lexer.offset)
	  }
    }
    
    current.size match 
    {
      case 0 => new AST // empty expression
      case 1 => {
        val ast = new AST
        ast.addChild(current.pop())
        ast
      }
      case _ => throw new RuntimeException("More than 1 AST node ("+current.size+") on stack ?")
    }
  }
  
  def expression() : Boolean = 
  {
    if ( term() ) 
    {
    	while ( lexer.peek( TokenType.PLUS ) || lexer.peek( TokenType.MINUS ) ) 
    	{
    	  if ( ! infixOp( expression ) ) {
    	    return false
    	  }
    	} 
    	return true  
    } 
   	failed("expression")
  }
  
  def term() : Boolean = 
  {    
    if ( factor() ) 
    {
	  while ( lexer.peek( TokenType.MULTIPLY ) || lexer.peek( TokenType.DIVIDE ) ) 
	  {		  
	    if ( ! infixOp( term ) ) {
	      return false
	    }
	  }
      return true
    }
    failed("term")
  }
  
  def infixOp( func : => () => Boolean ) : Boolean = 
  {
	  lexer.rememberState()		  
	  val operator = new OperatorNode( lexer.next() )
	  if ( ! func() ) 
	  {
	    lexer.recallState();
	    return failed("infixOp");
	  }
	  lexer.discardState()  
	  
	  val child2 = pop()
	  val child1 = pop()
	  operator.addChild( child1 )
	  operator.addChild( child2 )
	  push( operator )	  
	  true
  }  
  
  def factor() : Boolean = 
  {
    if ( parens() ) {
      return true
    }
    if ( lexer.peek( TokenType.NUMBER_LITERAL ) ) {
      push( new NumberNode( lexer.next() ) );
      return true
    }
    failed("factor")
  }

  private def push(node:ASTNode) :Unit = current.push(node)
  
  private def pop() : ASTNode = current.pop()
  
  def parens() : Boolean = 
  {
    if ( lexer.peek( TokenType.PARENS_OPEN ) ) 
    {
      lexer.rememberState()
      val operator = new OperatorNode( lexer.next(TokenType.PARENS_OPEN) )
      if ( ! expression() ) 
      {
        lexer.recallState()
        return failed("expr in parens")
      }
      if ( ! lexer.peek(TokenType.PARENS_CLOSE ) ) {
        lexer.recallState()
        throw new ParseException("Missing closing parens" , lexer.offset );
      }
      lexer.next(TokenType.PARENS_CLOSE)
      operator.addChild( pop() )
      push( operator )
      lexer.discardState()
      true
    } else {
      failed("parens open")
    }    
  }
  
  def failed(msg:String) : Boolean = false
}

object Calculator 
{
  def main(arg : Array[String] ) 
  {
    val frame = new JFrame("Calculator")
    val inputField = new JTextField()
    inputField.setPreferredSize( new Dimension(200,15 ) );
    val outputField = new JTextArea()
    outputField.setPreferredSize( new Dimension(200,200 ) );
    outputField.setEditable(false)
    
    inputField.addActionListener( new ActionListener() 
    { 
      override def actionPerformed(ev:ActionEvent) = 
      {
        try 
        {
            println("Parsing...")
            val ast = new ExpressionParser( inputField.getText() ).parse()
            println( "\nAST:\n"+ast.print() )
            val result = ast.evaluate()
            outputField.setText( result.toString )
        } 
        catch 
        {
          case e : ParseException => 
          {
            val msg = inputField.getText()+"\n"+" "*e.getErrorOffset()+"^ "+e.getMessage()
            outputField.setText( msg )          
          }
          case e : Exception => {
            e.printStackTrace()
            outputField.setText( "Something went terribly wrong..."+e.getMessage()+" ( "+e.getClass().getName()+")" )
          }
        }
      } 
    })
    
    frame.getContentPane().setLayout( new BorderLayout )
    frame.getContentPane().add( inputField , BorderLayout.NORTH )
    frame.getContentPane().add( new JScrollPane( outputField ) , BorderLayout.SOUTH )    
    frame.pack()
    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE)
    frame.setVisible(true)
  }
}