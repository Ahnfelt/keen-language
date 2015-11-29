package keencompiler

import java.util.regex.Matcher

import scala.collection.mutable.ArrayBuffer
import scala.util.matching.Regex

object Tokenizer {

    val pattern = ("^[ ]*(?:" + """
       ((?:[A-Z][a-zA-Z0-9]*[.])?[a-z][a-zA-Z0-9]*)(?![a-zA-Z0-9])
       ((?:[A-Z][a-zA-Z0-9]*[.])?[A-Z][a-zA-Z0-9]*)(?![a-zA-Z0-9])
       [#]js[ ]([^\r\n]+)
       ([#][a-zA-Z0-9]+)(?![a-zA-Z0-9])
       (\&\&|\|\|)
       ([(){}\[\]|])
       ([_,;:|]|[.][.]?|[-][>]|[<][-]|[=](?![=])|[&](?![&]))
       ([-+*][=])
       ([-+/*!])(?![=/*])
       ([>][=]?|[<][=]?|[!][=]|[=][=])
       (?:[']((?:[^']|[']['])*)['])(?!['])
       ([0-9]+)(?![0-9])
       \r?(\n)
       ([/][/][^\n]*|[/][*](?:[^*]|[*](?![/]))*[*][/])
    """.lines.map(_.trim).filter(_.nonEmpty).mkString("|") + ")[ ]*").r

    case class Position(line : Int, column : Int) {
        override def toString = "line " + line + ", column " + column
    }

    sealed abstract class Token(var position : Position = null)
    case class OutsideFile() extends Token
    case class Comment() extends Token
    case class LineBreak() extends Token
    case class Lower(text : String) extends Token
    case class Upper(text : String) extends Token
    case class Sharp(text : String) extends Token
    case class LeftRound() extends Token
    case class RightRound() extends Token
    case class LeftSquare() extends Token
    case class RightSquare() extends Token
    case class LeftCurly() extends Token
    case class RightCurly() extends Token
    case class Pipe() extends Token
    case class Minus() extends Token
    case class Plus() extends Token
    case class Slash() extends Token
    case class Star() extends Token
    case class Bang() extends Token
    case class AndAnd() extends Token
    case class OrOr() extends Token
    case class LessThan() extends Token
    case class LessThanOrEqual() extends Token
    case class GreaterThan() extends Token
    case class GreaterThanOrEqual() extends Token
    case class NotEqualTo() extends Token
    case class EqualTo() extends Token
    case class Comma() extends Token
    case class SemiColon() extends Token
    case class Dot() extends Token
    case class DotDot() extends Token
    case class Colon() extends Token
    case class Ampersand() extends Token
    case class ArrowLeft() extends Token
    case class ArrowRight() extends Token
    case class Underscore() extends Token
    case class Equals() extends Token
    case class MinusEquals() extends Token
    case class PlusEquals() extends Token
    case class StarEquals() extends Token
    case class JsSnippet(js : String) extends Token
    case class StringValue(text : String) extends Token
    case class IntegerValue(value : Long) extends Token

    def matchToToken(matcher : Regex.Match) : Token = {
        val Seq(lower, upper, js, sharp, andOr, bracket, punctuation, assign, operator, relation, single, integer, line, comment) = (1 to 14).map(matcher.group)
        if(lower != null) Lower(lower)
        else if(upper != null) Upper(upper)
        else if(sharp != null) Sharp(sharp.tail)
        else if(js != null) JsSnippet(js)
        else if(bracket != null) bracket match {
            case "(" => LeftRound()
            case ")" => RightRound()
            case "[" => LeftSquare()
            case "]" => RightSquare()
            case "{" => LeftCurly()
            case "}" => RightCurly()
            case "|" => Pipe()
            case t => throw new RuntimeException("Unknown token: " + t)
        }
        else if(assign != null) assign match {
            case "-=" => MinusEquals()
            case "+=" => PlusEquals()
            case "*=" => StarEquals()
            case t => throw new RuntimeException("Unknown token: " + t)
        }
        else if(operator != null) operator match {
            case "-" => Minus()
            case "+" => Plus()
            case "/" => Slash()
            case "*" => Star()
            case "!" => Bang()
            case t => throw new RuntimeException("Unknown token: " + t)
        }
        else if(andOr != null) andOr match {
            case "&&" => AndAnd()
            case "||" => OrOr()
            case t => throw new RuntimeException("Unknown token: " + t)
        }
        else if(relation != null) relation match {
            case "<" => LessThan()
            case "<=" => LessThanOrEqual()
            case ">" => GreaterThan()
            case ">=" => GreaterThanOrEqual()
            case "!=" => NotEqualTo()
            case "==" => EqualTo()
            case t => throw new RuntimeException("Unknown token: " + t)
        }
        else if(punctuation != null) punctuation match {
            case "," => Comma()
            case ";" => SemiColon()
            case "." => Dot()
            case ".." => DotDot()
            case ":" => Colon()
            case "&" => Ampersand()
            case "<-" => ArrowLeft()
            case "->" => ArrowRight()
            case "=" => Equals()
            case "_" => Underscore()
            case t => throw new RuntimeException("Unknown token: " + t)
        }
        else if(single != null) StringValue(single.replace("''", "'"))
        else if(integer != null) IntegerValue(integer.toLong)
        else if(line != null) LineBreak()
        else if(comment != null) Comment()
        else throw new RuntimeException("Unknown token: " + matcher.group(0))
    }

    def tokenize(text : String) : Array[Token] = {
        val brackets = ArrayBuffer[Token]()
        var lineBreak = false
        val tokens = ArrayBuffer[Token](OutsideFile(), OutsideFile(), OutsideFile())
        var currentText = text
        var matcher = pattern.findPrefixMatchOf(currentText)
        var lastToken : Token = OutsideFile()
        var lastEnd = 0
        var line = 1
        var column = 1
        while(matcher.isDefined) {
            val token = matchToToken(matcher.get)
            token.position = Position(line, column)
            if(token != Comment()) {
                if(token == LeftRound() || token == LeftSquare() || token == LeftCurly() || (token == Pipe() && brackets.lastOption.exists(_ != Pipe()))) {
                    brackets += token
                } else if(token == RightRound() || token == RightSquare() || token == RightCurly() || token == Pipe()) {
                    if(brackets.nonEmpty) brackets.remove(brackets.length - 1)
                }
                if(token != LineBreak()) {
                    if(lineBreak && lastToken != OutsideFile() && lastToken != Pipe() && lastToken != LeftCurly() && token != Pipe() && token != RightCurly()) tokens += LineBreak()
                    lineBreak = false
                    lastToken = token
                    tokens += token
                } else if(brackets.isEmpty || brackets.last == LeftCurly()) {
                    lineBreak = true
                }
            }
            lastEnd = matcher.get.end
            if(matcher.get.group(13) != null) {
                line += 1
                column = 1
            } else {
                column += lastEnd
            }
            // Doesn't work in JS for some reason: matcher.region(lastEnd, text.length)
            currentText = currentText.substring(lastEnd)
            matcher = pattern.findPrefixMatchOf(currentText)
        }
        if(currentText.nonEmpty) {
            throw new RuntimeException("Unexpected character: " + currentText.head)
        }
        tokens += OutsideFile()
        tokens += OutsideFile()
        tokens += OutsideFile()
        tokens.toArray
    }

    def main(args: Array[String]) {
        for(token <- tokenize(p1)) println(token)
    }

    val p1 = """
#import (_) = 'source/Base.keen'

Bool := [True, False]
Person := [Person(name : String, age : Int)]
List<A> := [Empty, Link(head : A, tail : List<A>)]
Option<A> := [None, Some(value : A)]

numbers : List<Int> = Link(head = 1, tail = Link(head = 2, tail = Empty))
add := {|x, y| x + y}
fac : Int -> Int = {
    |1| 1
    |i| i * fac(i - 1)
}
switch := {|value| {|cases| cases(value)}}

if := {|condition| {|then| {|else| switch(condition) {
    |True| then()
    |False| else()
}}}}

when := {|condition| {|body| if(condition)(body){} }}
unless := {|condition| {|body| if(condition){}(body) }}

abs := {|x, y|
    if(x > y) {
        x - y
    } {
        y - x
    }
}
each := {|list| {|body| switch(list) {
    |Link l|
        body(l.head)
        each(l.tail)(body)
    |Empty|
}}}
each(numbers) {|i|
    window.console.log(i)
}

Link xs := numbers
window.console.log(xs.head)
    """
}
