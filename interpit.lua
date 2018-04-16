-- interpit.lua
-- Corey S. Gray
-- 15 April 2018
--
-- For CS F331 / CSCE A331 Spring 2018
-- Interpret AST from parseit.parse
-- For Assignment 6, Exercise B

-- *******************************************************************
-- * To run a Dugong program, use dugong.lua (which uses this file). *
-- *******************************************************************

local interpit = {}  -- The module

-- ***** Variables *****
-- Symbolic Constants for AST

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

-- ***** Utility Functions *****
-- numberToInteger
-- Given a number, return the number rounded toward zero.
local function numberToInteger(n)
    assert(type(n) == "number")

    if n >= 0 then
        return math.floor(n)
    else
        return math.ceil(n)
    end
end


-- stringToInteger
-- Given a string, attempt to interpret it as an integer.
-- If this succeeds, return the integer. Otherwise, return 0.
local function stringToInteger(s)
    assert(type(s) == "string")

    -- Try to do string -> number conversion;
    -- make protected call (pcall), so we can handle errors.
    local success, value = pcall(function() return 0+s end)

    -- Return integer value, or 0 on error.
    if success then
        return numberToInteger(value)
    else
        return 0
    end
end


-- numberToString
-- Given a number, return its string form.
local function numberToString(n)
    assert(type(n) == "number")

    return ""..n
end

-- stringToBoolean
-- Given a string, return its Boolean.
local function stringToBoolean(s)
  assert(type(s) == "string")
  if s == "true" then
    return true
  else
    return false
  end
end

-- booleanToInteger
-- Given a boolean, return 1 if it is true or 0 if it is false.
local function booleanToInteger(b)
    assert(type(b) == "boolean")

    if b then
        return 1
    else
        return 0
    end
end


-- ***** Primary Function for Client Code *****

-- interp
-- Interpreter, given AST returned by parseit.parse.
-- Parameters:
--   ast     - AST constructed by parseit.parse
--   state   - Table holding Dugong variables & functions
--             - AST for function xyz is in state.f["xyz"]
--             - Value of simple variable xyz is in state.v["xyz"]
--             - Value of array item xyz[42] is in state.a["xyz"][42]
--   incall  - Function to call for line input
--             - incall() inputs line, returns string with no newline
--   outcall - Function to call for string output
--             - outcall(str) outputs str with no added newline
--             - To print a newline, do outcall("\n")
-- Return Value:
--   state, updated with changed variable values
function interpit.interp(ast, state, incall, outcall)
    -- Each local interpretation function is given the AST for the
    -- portion of the code it is interpreting. The function-wide
    -- versions of state, incall, and outcall may be used. The
    -- function-wide version of state may be modified as appropriate.
    
    -- interp_stmt_list
    -- AST: { STMT_LIST }
    function interp_stmt_list(ast)
        for i = 2, #ast do
            interp_stmt(ast[i])
        end
    end
    
    -- interp_stmt
    -- Takes a table corresponding to a statement AST and modifies the global state appropriately.
    -- Most ASTs start with an element identifying the statement, so this function is a series of cases based on what is the first element.
    function interp_stmt(ast)
        local name, body, str
        
        -- AST: { INPUT_STMT, lvalue }
        -- Dugong only takes SIMPLE_VAR which hold integers, so "lvalue" is the simple variable that the user will input.
        if ast[1] == INPUT_STMT then
            name = ast[2][2] -- lvalue
            body = incall()
            state.v[name] = stringToInteger(body)
        
        -- AST: { PRINT_STMT, arguments }
        -- arguments may be any combination of carriage returns, string literals, or expressions
        elseif ast[1] == PRINT_STMT then
            for i = 2, #ast do  -- skip the first element (PRINT_STMT) then proceed through arguemnts
                if ast[i][1] == CR_OUT then -- carriage return
                    outcall("\n")
                elseif ast[i][1] == STRLIT_OUT then -- string literals
                    str = ast[i][2]
                    outcall(str:sub(2, str:len() - 1))  -- remove quotes
                else -- expression
                    body = evaluateExpression(ast[2])
                    outcall(numberToString(body))
                end
            end
        
        -- AST: { FUNC_STMT, identifier, stmt_list }
        -- Creates/updates an entry in state's function table.
        elseif ast[1] == FUNC_STMT then
            name = ast[2] -- identifier
            body = ast[3] -- stmt_list
            state.f[name] = body
        
        -- AST: { CALL_FUNC, identifier }
        -- Retrieves a function from state's function table.
        elseif ast[1] == CALL_FUNC then
            name = ast[2] -- identifier
            body = state.f[name] -- Retrieves the function from the state's function table
            if body == nil then
                body = { STMT_LIST }  -- Default AST because Dugong does not throw fatal errors
            end
            interp_stmt_list(body)
        
        -- AST: { IF_STMT, condition, stmt_list }
        -- elseif adds additional conditions and stmt_lists: { IF_STMT, condition, stmt_list, condition, stmt_list }
        -- else adds an stmt_list without a condition: { IF_STMT, condition, stmt_list, stmt_list }
        -- There may be any number of elseif statements and else is always at the end
        elseif ast[1] == IF_STMT then
            local done = false
            local lastCondition = 2
            
            -- Start at first condition, end before final stmt_list (could be else), and check any additional conditions
            for i = 2, #ast - 1, 2 do
              -- if condition is not false and have not already executed an if statement
              if evaluateExpression(ast[i]) ~= 0 and not done then
                interp_stmt_list(ast[i + 1])
                done = true
              end
              -- save index of last condition
              lastCondition = i
            end
            
            -- if there is an else statement, which is two past last condition, and have not already executed an if statement
            if ast[lastCondition + 2] and not done then
              interp_stmt_list(ast[lastCondition + 2])
            end
        
        -- AST: { WHILE_STMT, condition, stmt_list }
        elseif ast[1] == WHILE_STMT then
          -- while condition is not false
          while evaluateExpression(ast[2]) ~= 0 do 
            interp_stmt_list(ast[3])
          end
        
        -- AST: {ASSN_STMT, expression }
        else
            processLValue(ast)
        end -- End statement cases
    end -- End interp_stmt

  -- processLValue
  -- LValues take the form: ID [ ‘[’ expr ‘]’ 
  -- Dugong only uses SIMPLE_VAR and ARRAY_VAR
  function processLValue(ast)
    local identifier, value
    
    -- AST: { SIMPLE_VAR, identifier, value }
    if ast[2][1] == SIMPLE_VAR then
      identifier = ast[2][2]
      value = evaluateExpression(ast[3])
      state.v[identifier] = numberToInteger(value)
    
    -- AST: { ARRAY_VAR, identifier[index], value }
    elseif ast[2][1] == ARRAY_VAR then
      identifier = ast[2][2]
      if state.a[identifier] == nil then -- replace nonexistent arrays with empty arrays
        state.a[identifier] = {}
      end
      value = evaluateExpression(ast[3])
      state.a[identifier][evaluateExpression(ast[2][3])] = value
    end
  end

  -- evaluateExpression
  function evaluateExpression(ast)
    local value
    
    -- Factor: Numeric Literal
    -- AST: { NUMLIT_VAL, integer }
    if ast[1] == NUMLIT_VAL then
      value = stringToInteger (ast[2])
    
    -- Factor: lvalue
    -- AST: { SIMPLE_VAR, identifier }
    elseif ast[1] == SIMPLE_VAR then
      value = state.v[ast[2]]
    
    -- Factor: lvalue
    -- AST: { ARRAY_VAR, identifier, index }
    elseif ast[1] == ARRAY_VAR then
      if state.a[ast[2]] ~= nil then
        value = state.a[ast[2]][evaluateExpression(ast[3])]
      else -- nonexistent array items are set to 0 as Dugong does not throw fatal errors
        value = 0
      end
    
    -- Factor: Boolean Literal
    -- AST: { BOOLLIT_VAL, true/false }
    elseif ast[1] == BOOLLIT_VAL then
      value = booleanToInteger(stringToBoolean(ast[2]))
    
    -- Factor: Function Call
    -- AST: { CALL_FUNC, identifier }
    elseif ast[1] == CALL_FUNC then
      interp_stmt(ast)
      value = state.v["return"]
    
    -- Comparison and Arithmetic Expressions
    elseif type(ast[1]) == "table" then
      -- Unary Operators
      -- AST: { { UN_OP, operator }, unary }
      if ast[1][1] == UN_OP then
        local unary = evaluateExpression(ast[2])
        
        -- Factor: Unary Operator +
        if ast[1][2] == "+" then
          value = unary
        
        -- Factor: Unary Operator -
        elseif ast[1][2] == "-" then
          value = -(unary)
        
        -- Comparison-Expression: Not
        elseif unary == 0 then
          value = 1
        else
          value = 0
        end -- Unary Operators
      
      -- Binary Operators
      -- AST: { { BIN_OP, operator }, lhs, rhs }
      elseif ast[1][1] == BIN_OP then
        local lhs = evaluateExpression(ast[2])
        local rhs = evaluateExpression(ast[3])
        
        -- Arithmetic Operators
        -- Most Dugong binary operators behave the same as Lua operators except that
        --   dividing or modulus by zero returns zero
        --   not-equal is != instead of ~=
        if ast[1][2] == "+" then
          value = lhs + rhs
          
        elseif ast[1][2] == "-" then
          value = lhs - rhs
        
        elseif ast[1][2] == "*" then
          value = lhs * rhs
        
        elseif ast[1][2] == "/" then
          if rhs == 0 then -- Dividing by 0
            value = 0
          else
            value = numberToInteger(lhs / rhs)
          end
          
        elseif ast[1][2] == "%" then
          if rhs == 0 then -- Modulus by 0
            value = 0
          else
            value = numberToInteger(lhs % rhs)
          end
        
        -- Comparison Operators
        elseif ast[1][2] == "==" then
          value = booleanToInteger(lhs == rhs)
        
        elseif ast[1][2] == "!=" then
          value = booleanToInteger(lhs ~= rhs)
          
        elseif ast[1][2] == "<" then
          value = booleanToInteger(lhs < rhs)
        
        elseif ast[1][2] == "<=" then
          value = booleanToInteger(lhs <= rhs)
        
        elseif ast[1][2] == ">" then
          value = booleanToInteger(lhs > rhs)
        
        elseif ast[1][2] == ">=" then
          value = booleanToInteger(lhs >= rhs)
        
        -- Logical And
        elseif ast[1][2] == "&&" then
          if lhs == 0 and rhs == 0 then
            value = 0
          else 
            value = booleanToInteger(lhs == rhs)
          end
        
        -- Logical Or
        elseif ast[1][2] == "||" then
          if lhs == 0 and rhs == 0 then
            value = 0
          else
            value = 1
          end
        end -- Binary Operators
      end -- Comparison and Arithmetic Expressions
    end -- expression cases   
    
    -- Empty expressions are evaluated as 0 since Dugong does not have fatal errors
    if value == nil then
      value = 0
    end 
    
    return value
  end-- evaluateExpression

  
  -- Body of function interp
  interp_stmt_list(ast)
  return state
end -- interpit.interp

-- ***** Module Export *****
return interpit
