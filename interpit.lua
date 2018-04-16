-- interpit.lua  INCOMPLETE
-- Glenn G. Chappell
-- 29 Mar 2018
-- Updated 2 Apr 2018
--
-- For CS F331 / CSCE A331 Spring 2018
-- Interpret AST from parseit.parse
-- For Assignment 6, Exercise B


-- *******************************************************************
-- * To run a Dugong program, use dugong.lua (which uses this file). *
-- *******************************************************************


local interpit = {}  -- Our module


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


-- numToInt
-- Given a number, return the number rounded toward zero.
local function numToInt(n)
    assert(type(n) == "number")

    if n >= 0 then
        return math.floor(n)
    else
        return math.ceil(n)
    end
end


-- strToNum
-- Given a string, attempt to interpret it as an integer. If this
-- succeeds, return the integer. Otherwise, return 0.
local function strToNum(s)
    assert(type(s) == "string")

    -- Try to do string -> number conversion; make protected call
    -- (pcall), so we can handle errors.
    local success, value = pcall(function() return 0+s end)

    -- Return integer value, or 0 on error.
    if success then
        return numToInt(value)
    else
        return 0
    end
end


-- numToStr
-- Given a number, return its string form.
local function numToStr(n)
    assert(type(n) == "number")

    return ""..n
end

-- strToBool
-- Given a string, return its Boolean.
local function strToBool(s)
  assert(type(s) == "string")
  if s == "true" then
    return true
  else
    return false
  end
end

-- boolToInt
-- Given a boolean, return 1 if it is true, 0 if it is false.
local function boolToInt(b)
    assert(type(b) == "boolean")

    if b then
        return 1
    else
        return 0
    end
end


-- astToStr
-- Given an AST, produce a string holding the AST in (roughly) Lua form,
-- with numbers replaced by names of symbolic constants used in parseit.
-- A table is assumed to represent an array.
-- See the Assignment 4 description for the AST Specification.
--
-- THIS FUNCTION IS INTENDED FOR USE IN DEBUGGING ONLY!
-- IT SHOULD NOT BE CALLED IN THE FINAL VERSION OF THE CODE.
function astToStr(x)
    local symbolNames = {
        "STMT_LIST", "INPUT_STMT", "PRINT_STMT", "FUNC_STMT",
        "CALL_FUNC", "IF_STMT", "WHILE_STMT", "ASSN_STMT", "CR_OUT",
        "STRLIT_OUT", "BIN_OP", "UN_OP", "NUMLIT_VAL", "BOOLLIT_VAL",
        "SIMPLE_VAR", "ARRAY_VAR"
    }
    if type(x) == "number" then
        local name = symbolNames[x]
        if name == nil then
            return "<Unknown numerical constant: "..x..">"
        else
            return name
        end
    elseif type(x) == "string" then
        return '"'..x..'"'
    elseif type(x) == "boolean" then
        if x then
            return "true"
        else
            return "false"
        end
    elseif type(x) == "table" then
        local first = true
        local result = "{"
        for k = 1, #x do
            if not first then
                result = result .. ","
            end
            result = result .. astToStr(x[k])
            first = false
        end
        result = result .. "}"
        return result
    elseif type(x) == "nil" then
        return "nil"
    else
        return "<"..type(x)..">"
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

    function interp_stmt_list(ast)
        for i = 2, #ast do
            interp_stmt(ast[i])
        end
    end

    function interp_stmt(ast)
        local name, body, str

        if ast[1] == INPUT_STMT then
            if ast[2][1] == SIMPLE_VAR then
              name = ast[2][2]
              body = incall()
              state.v[name] = numToInt(strToNum(body))
            end
        
        elseif ast[1] == PRINT_STMT then
            for i = 2, #ast do
                if ast[i][1] == CR_OUT then
                    outcall("\n")
                elseif ast[i][1] == STRLIT_OUT then
                    str = ast[i][2]
                    outcall(str:sub(2,str:len()-1))  -- Remove quotes
                else
                    body = evalExpr(ast[2])
                    outcall(numToStr(body))
                end
            end
        
        elseif ast[1] == FUNC_STMT then
            name = ast[2]
            body = ast[3]
            state.f[name] = body
        
        elseif ast[1] == CALL_FUNC then
            name = ast[2]
            body = state.f[name]
            if body == nil then
                body = { STMT_LIST }  -- Default AST
            end
            interp_stmt_list(body)
        
        elseif ast[1] == IF_STMT then
            local done = false
            local elseIndex = 0
            
            for i = 2, #ast - 1, 2 do
              if evalExpr(ast[i]) ~= 0 and not done then
                interp_stmt_list(ast[i + 1])
                done = true
              end
              elseIndex = i
            end
              
            if ast[elseIndex + 2] and not done then
              interp_stmt_list(ast[elseIndex + 2])
            end
            
        elseif ast[1] == WHILE_STMT then
            while evalExpr(ast[2]) ~= 0 do
              interp_stmt_list(ast[3])
            end
            
        else
            assert(ast[1] == ASSN_STMT)
            processLValue(ast)
        end
    end

  function processLValue(ast)
    local name, body
    
    if ast[2][1] == SIMPLE_VAR then
      name = ast[2][2]
      body = evalExpr(ast[3])
      state.v[name] = numToInt(body)
      
    elseif ast[2][1] == ARRAY_VAR then
      name = ast[2][2]
      if state.a[name] == nil then
        state.a[name] = {}
      end
      body = evalExpr(ast[3])
      state.a[name][evalExpr(ast[2][3])] = body
    end
  end

  function evalExpr(ast)
    local value
    
    if ast[1] == NUMLIT_VAL then
      value = strToNum (ast[2])
      
    elseif ast[1] == SIMPLE_VAR then
      value = state.v[ast[2]]
      
    elseif ast[1] == ARRAY_VAR then
      if state.a[ast[2]] ~= nil then
        value = state.a[ast[2]][evalExpr(ast[3])]
      else
        value = 0
      end
      
    elseif ast[1] == BOOLLIT_VAL then
      value = boolToInt(strToBool(ast[2]))
      
    elseif ast[1] == CALL_FUNC then
      interp_stmt(ast)
      value = state.v["return"]
    
    elseif type(ast[1]) == "table" then
      if ast[1][1] == UN_OP then
        local unary = evalExpr(ast[2])
        
        if ast[1][2] == "+" then
          value = unary
          
        elseif ast[1][2] == "-" then
          value = -(unary)
        
        elseif unary == 0 then
          value = 1
        
        else
          value = 0
        end
        
      elseif ast[1][1] == BIN_OP then
        local lhs = evalExpr(ast[2])
        local rhs = evalExpr(ast[3])
        local bool = lhs == rhs
        
        -- Arithmetic Operators
        if ast[1][2] == "+" then
          value = lhs + rhs
          
        elseif ast[1][2] == "-" then
          value = lhs - rhs
        
        elseif ast[1][2] == "*" then
          value = lhs * rhs
        
        elseif ast[1][2] == "/" then
          if rhs == 0 then
            value = 0
          else
            value = numToInt(lhs / rhs)
          end
          
        elseif ast[1][2] == "%" then
          if rhs == 0 then
            value = 0
          else
            value = numToInt(lhs % rhs)
          end
        
        -- Comparison Operators
        elseif ast[1][2] == "==" then
          value = boolToInt(lhs == rhs)
        
        elseif ast[1][2] == "!=" then
          value = boolToInt(lhs ~= rhs)
          
        elseif ast[1][2] == "<" then
          value = boolToInt(lhs < rhs)
        
        elseif ast[1][2] == "<=" then
          value = boolToInt(lhs <= rhs)
        
        elseif ast[1][2] == ">" then
          value = boolToInt(lhs > rhs)
        
        elseif ast[1][2] == ">=" then
          value = boolToInt(lhs >= rhs)
        
        -- Logical Operatos
        elseif ast[1][2] == "&&" then
          if lhs == 0 and rhs == 0 then
            value = 0
          else 
            value = boolToInt(bool)
          end
          
        elseif ast[1][2] == "||" then
          if lhs == 0 and rhs == 0 then
            value = 0
          elseif lhs ~= 0 or rhs ~= 0 then
            value =1
          else
            value = boolToInt(bool)
          end
        end
      end
    end    
    
    if value == nil then
      return 0
    else
      return value
    end
  end

  
  -- Body of function interp
  interp_stmt_list(ast)
  return state
end

-- ***** Module Export *****
return interpit
