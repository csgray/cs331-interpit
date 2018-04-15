-- parseit.lua
-- Corey Gray
-- 25 February 2018
-- Source for parseit module for CS 331: Assignment 4 which is a recursive-descent parser
-- Heavily based on "rdparser4.lua" by Glenn G. Chappell
-- Requires lexit.lua

-- Grammar (with line numbers)
-- (01) program     →  	stmt_list
-- (02) stmt_list   →  	{ statement }
-- (03) statement   →  	‘input’ lvalue
-- (04)             |  	‘print’ print_arg { ‘;’ print_arg }
-- (05)             |  	‘func’ ID stmt_list ‘end’
-- (06)             |  	‘call’ ID
-- (07)             |  	‘if’ expr stmt_list { ‘elseif’ expr stmt_list } [ ‘else’ stmt_list ] ‘end’
-- (08)             |  	‘while’ expr stmt_list ‘end’
-- (09)             |  	lvalue ‘=’ expr
-- (10) print_arg   →  	‘cr’
-- (11)             |  	STRLIT
-- (12)             |  	expr
-- (13) expr        →  	comp_expr { ( ‘&&’ | ‘||’ ) comp_expr }
-- (14) comp_expr   →  	‘!’ comp_expr
-- (15)             |  	arith_expr { ( ‘==’ | ‘!=’ | ‘<’ | ‘<=’ | ‘>’ | ‘>=’ ) arith_expr }
-- (16) arith_expr  →  	term { ( ‘+’ | ‘-’ ) term }
-- (17) term        →  	factor { ( ‘*’ | ‘/’ | ‘%’ ) factor }
-- (18) factor      →  	‘(’ expr ‘)’
-- (19)             |  	( ‘+’ | ‘-’ ) factor
-- (20)             |  	‘call’ ID
-- (21)             |  	NUMLIT
-- (22)             |  	( ‘true’ | ‘false’ )
-- (23)             |  	lvalue
-- (24) lvalue      →  	ID [ ‘[’ expr ‘]’ ]
--
-- The following binary operators are left-associative:
-- &&, ||, ==, !=, <, <=, >, >=, binary +, binary -, *, /, %

local parseit = {}
lexit = require "lexit"

-- Symbolic Constants for Abstract Syntax Tree (AST)
local STMT_LIST   = 1
local INPUT_STMT  = 2
local PRINT_STMT  = 3
local FUNC_STMT   = 4
local CALL_FUNC   = 5
local IF_STMT     = 6
local WHILE_STMT  = 7
local ASSN_STMT   = 8
local CR_OUT      = 9
local STRLIT_OUT  = 10
local BIN_OP      = 11
local UN_OP       = 12
local NUMLIT_VAL  = 13
local BOOLLIT_VAL = 14
local SIMPLE_VAR  = 15
local ARRAY_VAR   = 16

-- Variables

-- For lexer iteration
local iterator          -- Iterator returned by lexit.lex
local state             -- State for above iterator
local lexerOutString    -- First value returned from iterator
local lexerOutCategory  -- Second value returned from iterator

-- For current lexeme
local lexemeString = ""
local lexemeCategory = 0

-- Utility Functions

-- advance
-- Go to the next lexeme and load it into lexemeString, lexemeCategory.
-- Should be called once before any parsing is done.
-- Function initialize must be called before this function is called.
local function advance()
  lexerOutString, lexerOutCategory = iterator(state, lexerOutString)
  
  -- Check for conditions requiring prefering an operator
  if lexerOutCategory == lexit.ID or
     lexerOutCategory == lexit.NUMLIT or
     lexerOutString == "]" or
     lexerOutString == ")" or
     lexerOutString == "true" or
     lexerOutString == "false" then
       lexit.preferOp()
  end
  
  -- If we're not past the end, copy current lexeme into variables
  if lexerOutString ~= nil then
    lexemeString, lexemeCategory = lexerOutString, lexerOutCategory
  else
    lexemeString, lexemeCategory = "", 0
  end
end

-- initialize
-- Initial call. Sets the input for parsing functions.
local function initialize(program)
  iterator = lexit.lex(program)
  advance()
end

-- atEnd
-- Return true if position has reached end of input.
-- Function init must be called before this function is called.
local function atEnd()
  return lexemeCategory == 0
end

-- matchString
-- Sees if current lexemeString is equal to given string.
-- If it is, advances to the next lexeme and returns true.
-- If it is not, then does not advance and returns false.
-- Function initialize must be called before this function is called.
local function matchString(string)
  if lexemeString == string then
    advance()
    return true
  else
    return false
  end
end

-- matchCategory
-- Sees if current lexemeCategory is equal to given lexeme category (integer).
-- If it is, advances to the next lexeme and returns true.
-- If it is not, does not advance and returns false.
-- Function initialize must be called before this function is called.
local function matchCategory(category)
  if lexemeCategory == category then
    advance()
    return true
  else
    return false
  end
end

-- Primary Function for Client Code

-- parse
-- Takes a program and returns two booleans and the AST.
-- Boolean 'good' indicates whether the parsing was succesful.
-- Boolean 'done' indicates whether the parser reached the end of the input.
-- The AST is only valid if both booleans are true.
function parseit.parse(program)
  initialize(program)
  local good, abstractSyntaxTree = parse_program()
  local done = atEnd()
  return good, done, abstractSyntaxTree
end

-- Parsing Functions
-- Each of the following is a parsing function for a nonterminal in the grammar.
-- Each function parses the nonterminal in its name and returns a pair: boolean, AST.
-- On a successful parse, the boolean is true, the AST is valid,
-- and the current lexeme is just past the end of the string the nonterminal expanded into.
-- Otherwise, the boolean is false, the AST is not valid, and no guarantees are made about the current lexeme.
-- "(line number) nonterminal" identifiers the line of the grammar.

-- parse_program
-- Parsing function for nonterminal "program"
-- Function initialize must be called before this function is called.
function parse_program()
  -- (01) Program (start symbol)
  local good, ast = parse_stmt_list()
  return good, ast
end

-- parse_stmt_list
-- Parsing function for nonterminal "stmt_list"
-- Function initialize must be called before this function is called.
function parse_stmt_list()
  -- (02) Statement-List
  local good, ast1, ast2
  ast1 = { STMT_LIST }
  
  while true do
    if lexemeString ~= "input"
      and lexemeString ~= "print"
      and lexemeString ~= "func"
      and lexemeString ~= "call"
      and lexemeString ~= "if"
      and lexemeString ~= "while"
      and lexemeCategory ~= lexit.ID then
        return true, ast1
    end
    good, ast2 = parse_statement()
    if not good then
      return false, nil
    end
    table.insert(ast1, ast2)
  end
end

-- parse_statement
-- Parsing function for nonterminal "statement"
-- Function initialize must be called before this function is called.
function parse_statement()
  local good, ast1, ast2, ast3, saveLexeme
    
  -- (03) Statement: Input
  if matchString("input") then
    good, ast1 = parse_lvalue()
    if not good then
      return false, nil
    end
    return true, { INPUT_STMT, ast1 }
    
  -- (04) Statement: Print
  elseif matchString("print") then
    good, ast1 = parse_print_arg()
    if not good then
      return false, nil
    end
    
    ast2 = { PRINT_STMT, ast1 }
    
    while true do
      if not matchString(";") then
        break
      end
      good, ast1 = parse_print_arg()
      if not good then
        return false, nil
      end
      table.insert(ast2, ast1)
    end
    
    return true, ast2
  
  -- (05) Statement: Function Definition
  elseif matchString("func") then
    saveLexeme = lexemeString
    if matchCategory(lexit.ID) then
      good, ast1 = parse_stmt_list()
      if not good then
        return false, nil
      end
      
      ast2 = { FUNC_STMT, saveLexeme, ast1 }      
      if matchString("end") then
        return true, ast2
      end
    end  
    
  -- (06) Statement: Function Call
  elseif matchString("call") then
    saveLexeme = lexemeString
    if not matchCategory(lexit.ID) then
      return false, nil
    end
    ast1 = { CALL_FUNC, saveLexeme }
    return true, ast1
  
  -- (07) Statement: If
  elseif matchString("if") then
    good, ast1 = parse_expr()
    if not good then
      return false, nil
    end
    
    good, ast2 = parse_stmt_list()
    if not good then
      return false, nil
    end
    
    ast3 = { IF_STMT, ast1, ast2 }
    
    while matchString("elseif") do
      good, ast1 = parse_expr()
      if not good then
        return false, nil
      end
      
      good, ast2 = parse_stmt_list()
      if not good then
        return false, nil
      end
      
      table.insert(ast3, ast1)
      table.insert(ast3, ast2)
    end
    
    if matchString("else") then
      good, ast1 = parse_stmt_list()
      if not good then
        return false, nil
      end
      
      table.insert(ast3, ast1)
    end
  
    if matchString("end") then
      return true, ast3
    end 
  
  -- (08) Statement: While
  elseif matchString("while") then
    good, ast1 = parse_expr()
    if not good then
      return false, nil
    end
    
    good, ast2 = parse_stmt_list()
    if not good then
      return false, nil
    end
    
    ast3 = { WHILE_STMT, ast1, ast2 }
    if matchString("end") then
      return true, ast3
    end   
  
  -- (09) Statement: Assignment
  elseif lexemeCategory == lexit.ID then
    good, ast1 = parse_lvalue()
    if not good then
      return false, nil
    end
    ast2 = {ASSN_STMT, ast1 }
    
    if matchString("=") then
      good, ast1 = parse_expr()
      if not good then
        return false, nil
      end
      table.insert(ast2, ast1)
      return true, ast2
    end
  end
  
  return false, nil
end -- end parse_statement()

-- parse_print_arg()
-- Parsing function for nonterminal "print_arg"
-- Function initialize must be called before this function is called.
function parse_print_arg()
  local good, ast, saveLexeme
  saveLexeme = lexemeString
  
  -- (10) Print-Argument: Carriage-Return
  if matchString("cr") then
    ast = { CR_OUT }
  
  -- (11) Print-Argument: StringLiteral
  elseif matchCategory(lexit.STRLIT) then
    ast = {STRLIT_OUT, saveLexeme }

  -- (12) Print-Argument: Expression
  else 
    good, ast = parse_expr()
    if not good then
      return false, nil
    end
  end 

  return true, ast
end

-- parse_expr
-- Parsing function for nonterminal "expr"
-- Function initialize must be called before this function is called.
function parse_expr()
  local good, ast1, ast2, saveOperator
  
  -- (13) Expression
  good, ast1 = parse_comp_expr()
  if not good then
    return false, nil
  end
  
  while true do
    saveOperator = lexemeString
    if not matchString("&&") and
       not matchString("||") then
         break
    end
    
    good, ast2 = parse_comp_expr()
    if not good then
      return false, nil
    end   
    ast1 = { { BIN_OP, saveOperator }, ast1, ast2 }
  end
    
  return true, ast1
end

-- parse_comp_expr
-- Parsing function for nonterminal "comp_expr"
-- Function initialize must be called before this function is called.
function parse_comp_expr()
  local good, ast1, ast2, saveOperator
  
  -- (14) Comparison-Expression: Not
  if matchString("!") then
    good, ast1 = parse_comp_expr()
    if not good then
      return false, nil
    end
    ast2 = { { UN_OP, "!"}, ast1 }
    return true, ast2
  end
  
  -- (15) Comparison-Expression: Arithmetic-Expression
  good, ast1 = parse_arith_expr()
  if not good then
    return false, nil
  end
  
  while true do
    saveOperator = lexemeString
    if not matchString("==") and
       not matchString("!=") and 
       not matchString("<") and
       not matchString("<=") and
       not matchString(">") and
       not matchString(">=") then
         break
    end
    
    good, ast2 = parse_arith_expr()
    if not good then
      return false, nil
    end

    ast1 = { { BIN_OP, saveOperator }, ast1, ast2 }
  end
  
  return true, ast1
end

-- parse_arith_expr
-- Parsing function for nonterminal "arith_expr"
-- Function initialize must be called before this function is called.
function parse_arith_expr()
  local good, ast1, ast2, saveOperator
  -- (16) Arithmetic-Expression
  good, ast1 = parse_term()
  if not good then
    return false, nil
  end
  
  while true do
    saveOperator = lexemeString
    if not matchString("+") and
       not matchString("-") then
         break
    end
    
    good, ast2 = parse_term()
    if not good then
      return false, nil
    end
    ast1 = { { BIN_OP, saveOperator }, ast1, ast2 }
  end
  
  return true, ast1
end

-- parse_term
-- Parsing function for nonterminal "term"
-- Function initialize must be called before this function is called.
function parse_term()
  local good, ast1, ast2, saveOperator
  -- (17) Term
  good, ast1 = parse_factor()
  if not good then
    return false, nil
  end

  while true do
    saveOperator = lexemeString
    if not matchString("*") and
       not matchString("/") and 
       not matchString("%") then
         break
    end

    good, ast2 = parse_factor()
    if not good then
      return false, nil
    end
    ast1 = { { BIN_OP, saveOperator }, ast1, ast2 }
  end

  return true, ast1  
end

-- parse_factor
-- Parsing function for nonterminal "factor"
-- Function initialize must be called before this function is called.
function parse_factor()
  local good, ast1, ast2, saveLexeme
  saveLexeme = lexemeString
  -- (18) Factor: Parenthesized Expression
  if matchString("(") then
    good, ast1 = parse_expr()
    if not good then
      return false, nil
    end
    if not matchString(")") then
      return false, nil
    end
    return true, ast1
    
  -- (19) Factor: Unary Operator
  elseif matchString("+") or
         matchString("-") then
           good, ast1 = parse_factor()
           if not good then
             return false, nil
           end
           ast2 = { { UN_OP, saveLexeme }, ast1 }
           return true, ast2
  
  -- (20) Factor: Function Call
  elseif matchString("call") then
    saveLexeme = lexemeString
    if not matchCategory(lexit.ID) then
      return false, nil
    end
    ast1 = { CALL_FUNC, saveLexeme }
    return true, ast1
  
  -- (21) Factor: NumericLiteral
  elseif matchCategory(lexit.NUMLIT) then
    ast1 = { NUMLIT_VAL, saveLexeme }
    return true, ast1
    
  -- (22) Factor: Boolean Literal
  elseif matchString("true") or 
         matchString("false") then
    ast1 = { BOOLLIT_VAL, saveLexeme }
    return true, ast1
  
  -- (23) Factor: L-Value
  else
    good, ast1 = parse_lvalue()
    if not good then
      return false, nil
    end
    return true, ast1
  end
end

-- parse_lvalue
-- Parsing function for nonterminal "lvalue"
-- Function initialize must be called before this function is called.
function parse_lvalue()
  local good, ast1, ast2, saveLexeme
  saveLexeme = lexemeString
  
  if matchCategory(lexit.ID) then
    ast1 = { SIMPLE_VAR, saveLexeme }
    
    if matchString("[") then
      good, ast2 = parse_expr()    
      if not good then
        return false, nil
      end
      if not matchString("]") then
        return false, nil
      end
    
      ast1 = { ARRAY_VAR, saveLexeme, ast2 }
    end
  return true, ast1  
  end
  
  return false, nil
end

return parseit