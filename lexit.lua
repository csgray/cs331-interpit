-- lexit.lua
-- Corey Gray
-- 20 February 2018
-- Source for lexit module for CS 331: Assignment 3B which is a lexer
-- Heavily based on "lexer.lua" by Glenn G. Chappell

local lexit = {}

-- ****
-- Public Constants
-- ****

-- Numeric constants representing lexeme categories
lexit.KEY = 1
lexit.ID = 2
lexit.NUMLIT = 3
lexit.STRLIT = 4
lexit.OP = 5
lexit.PUNCT = 6
lexit.MAL = 7

-- catnames
-- Array of names of lexeme categories.
-- Human-readable strings. Indices are above numeric constants.
lexit.catnames = {
  "Keyword",
  "Identifier",
  "NumericLiteral",
  "StringLiteral",
  "Operator",
  "Punctuation",
  "Malformed"
  }

-- ****
-- Variables
-- ****

-- Indicates that the next lexeme, if it begins with + or -, should always be interpreted as an operator.
local preferOpFlag = false;

-- ****
-- Kind-of-Character Functions
-- ****

-- isLetter
-- Returns true if string character is a letter character, false otherwise.
local function isLetter(character)
  if character:len() ~= 1 then
    return false
  elseif character >= "A" and character <= "Z" then
    return true
  elseif character >= "a" and character <= "z" then
    return true
  else
    return false
  end
end

-- isDigit
-- Returns true if string character is a digit character, false otherwise.
local function isDigit(character)
  if character:len() ~= 1 then
    return false
  elseif character >= "0" and character <= "9" then
    return true
  else
    return false
  end
end

-- isWhitespace
-- Returns true if string character is a whitespace character, false otherwise.
local function isWhitespace(character)
  if character:len() ~= 1 then
    return false
  elseif character == " " or    -- space
         character == "\t" or   -- tab
         character == "\v" or   -- vertical-tab
         character == "\n" or   -- new-line
         character == "\r" or   -- carriage-return
         character == "\f" then -- form-feed
    return true
  else
    return false
  end
end

-- isIllegal
-- Returns true if string character is an illegal character, false otherwise
local function isIllegal(character)
  if character:len() ~= 1 then
    return false
  elseif isWhitespace(character) then
    return false
  elseif character >= " " and character <= "~" then -- ASCII 032 through 126
    return false
  else
    return true
  end
end

-- ****
-- Exported Lexer Functions
-- ****

-- preferOp
-- Takes no parameters and returns nothing.
-- If this function is called just before a loop iteration, then, on that iteration, the lexer prefers to return an operator, rather than a number.
function lexit.preferOp()
  preferOpFlag = true;
end

-- lex
-- Takes a string parameter and allows for for-in iteration
-- through lexemes in the passed string
function lexit.lex(program)
  
  -- **** Variables ****
  local position 
  local state
  local character
  local lexeme
  local category
  local handlers
  local stringQuote -- the sort of quote used to start the string
  
  -- **** States Constants ****
  local DONE = 0
  local START = 1
  local LETTER = 2
  local DIGIT = 3
  local EXPONENT = 4
  local PLUSMINUS = 5
  local STRING = 6
  local COMPARISON = 7
  local AMPERSAND = 8
  local PIPE = 9
  
  -- **** Character-Related Utility Functions ****
  
  -- currentCharacter
  -- Returns the current character at index position in program.
  -- Return value is a single-character string or the empty string if position is past the end.
  local function currentCharacter()
    return program:sub(position, position)
  end
  
  -- nextCharacter
  -- Return the next character at index position+1 in program.
  -- Return value is a single-character string or the empty string if position is past the end.
  local function nextCharacter()
    return program:sub(position+1, position+1)
  end
  
  -- nextNextCharacter
  -- Return the character after the next character at index position+2 in program.
  -- Return value is a single-character string or the empty string if position is past the end.
  local function nextNextCharacter()
    return program:sub(position+2, position+2)
  end
  
  -- drop1
  -- Move position to the next character.
  local function drop1()
    position = position+1
  end
  
  -- add1
  -- Add the current character to the lexeme, moving position to the next character.
  local function add1()
    lexeme = lexeme .. currentCharacter()
    drop1()
  end
  
  -- skipWhitespace
  -- Skip whitespace and comments by moving position to the beginning of the next lexeme or to program:len()+1.
  local function skipWhitespace()
    while true do
      -- Advance position if whitespace
      while isWhitespace(currentCharacter()) do
        drop1()
      end
      
      -- Exit if not comment
      if currentCharacter() ~= "#" then
        break
      end
      
      -- Drop comment character
      drop1()
      
      -- Advance to end of line or program which finishes comment
      while true do
        if currentCharacter() == "\n" then
          break
        elseif currentCharacter() == "" then
          return
        end
        drop1()
      end
    end
  end
  
  -- **** State-Handler Functions ****
  
  -- handle_DONE
  -- Detects if the lexer tries to erroneously handle the DONE state.
  local function handle_DONE()
    io.write("ERROR: 'DONE' state should not be handled.\n")
    assert(0)
  end
  
  -- handle_START
  -- Called at the beginning of each new lexeme.
  local function handle_START()
    if isIllegal(character) then
      add1()
      state = DONE
      category = lexit.MAL
    elseif isLetter(character) or character == "_" then
      add1()
      state = LETTER
    elseif isDigit(character) then
      add1()
      state = DIGIT
    elseif character == "+" or character == "-" then
      add1()
      state = PLUSMINUS
    elseif character == "'" or character == '"' then
      stringQuote = character
      add1()
      state = STRING
    elseif character == "=" or
           character == "!" or
           character == "<" or
           character == ">" then
      add1()
      state = COMPARISON
    elseif character == "&" then
      add1()
      state = AMPERSAND
    elseif character == "|" then
      add1()
      state = PIPE
    elseif character == "*" or
           character == "/" or
           character == "%" or
           character == "[" or
           character == "]" or
           character == ";" then
      add1()
      state = DONE
      category = lexit.OP
    else
      add1()
      state = DONE
      category = lexit.PUNCT
    end
  end

  -- handle_LETTER()
  -- Determines if a lexeme is a keyword or identifier.
  local function handle_LETTER()
    if isLetter(character) or isDigit(character) or character == "_" then
      add1()
    else
      state = DONE
      if lexeme == "call" or
         lexeme == "cr" or
         lexeme == "else" or
         lexeme == "elseif" or
         lexeme == "end" or
         lexeme == "false" or
         lexeme == "func" or
         lexeme == "if" or
         lexeme == "input" or
         lexeme == "print" or 
         lexeme == "true" or
         lexeme == "while" then
           category = lexit.KEY
      else
        category = lexit.ID
      end
    end
  end
       
  -- handle_DIGIT()
  -- Determines if a lexeme is a NumericLiteral.
  local function handle_DIGIT()
    if isDigit(character) then
      add1()
    
    -- Handle possible exponents  
    elseif character == "e" or character == "E" then
      if isDigit(nextCharacter()) then
        add1() -- add e or E
        add1() -- add digit
        state = EXPONENT
      elseif nextCharacter() == "+" then
        if isDigit(nextNextCharacter()) then
          add1() -- add e or E
          add1() -- add +
          add1() -- add digit
          state = EXPONENT
        else
          state = DONE
          category = lexit.NUMLIT
        end
      else
        state = DONE
        category = lexit.NUMLIT
      end
    
    -- No more digits and not an exponent
    else
      state = DONE
      category = lexit.NUMLIT
    end
  end

  -- handle_EXPONENT
  -- Determines when an exponent in a NumericLiteral ends.
  local function handle_EXPONENT()
    if isDigit(character) then
      add1()
      state = EXPONENT
    else
      state = DONE
      category = lexit.NUMLIT
    end
  end
  
  -- handle_PLUSMINUS
  -- Determines if + or - is an operator or part of a NumericLiteral
  local function handle_PLUSMINUS()
    if isDigit(character) and preferOpFlag == false then
      add1()
      state = DIGIT
    else
      state = DONE
      category = lexit.OP
    end
  end

  -- handle_STRING
  -- Determines if a lexeme is a StringLiteral
  local function handle_STRING()
    if character == stringQuote then
      add1()
      state = DONE
      category = lexit.STRLIT
    elseif character ~= "\n" and character ~= "" then
      add1()
      state = STRING
    else
      add1()
      state = DONE
      category = lexit.MAL
    end
  end
  
  -- handle_COMPARISON
  -- Handles =, !, <, and > which are all operators but may be followed by =
  local function handle_COMPARISON()
    if character == "=" then
      add1()
    end
    state = DONE
    category = lexit.OP
  end

  -- handle_AMPERSAND
  -- Checks if & is followed by & for an operator
  local function handle_AMPERSAND()
    if character == "&" then
      add1()
      state = DONE
      category = lexit.OP 
    else
      state = DONE
      category = lexit.PUNCT
    end
  end
  
  -- handle_PIPE
  -- Checks if | is followed by | for an operator
  local function handle_PIPE()
    if character == "|" then
      add1()
      state = DONE
      category = lexit.OP 
    else
      state = DONE
      category = lexit.PUNCT
    end
  end

  -- **** Table of State-Handler Functions ****
  -- Index corresponds with the State Constants.
  handlers = {
      [DONE]=handle_DONE,
      [START]=handle_START,
      [LETTER]=handle_LETTER,
      [DIGIT]=handle_DIGIT,
      [EXPONENT]=handle_EXPONENT,
      [PLUSMINUS]=handle_PLUSMINUS,
      [STRING]=handle_STRING,
      [COMPARISON]=handle_COMPARISON,
      [AMPERSAND]=handle_AMPERSAND,
      [PIPE]=handle_PIPE
  }
  
  -- **** Iterator Function ****
  -- getLexeme
  -- Called each time through the for-in loop.
  -- Returns a pair: lexeme (string), category (int) or nil, nil if no more lexeme.
  local function getLexeme(dummy1, dummy2)
    -- End of program
    if position > program:len() then
      preferOpFlag = false
      return nil, nil
    end
    
    -- Beginning of a new lexeme
    lexeme  = ""
    state = START
    while state ~= DONE do
      character = currentCharacter()
      handlers[state]()
    end
    
    -- Finish lexeme
    skipWhitespace()
    preferOpFlag = false
    return lexeme, category
  end
  
  -- **** Body of Function Lexit
  -- Initialize and return the iterator function
  position = 1
  skipWhitespace()
  return getLexeme, nil, nil
end -- End of lexit.lex
  
-- ****
-- Module Table Return
-- ****
return lexit
