#!/usr/bin/env lua
-- interpit_test.lua
-- Glenn G. Chappell
-- 3 Apr 2018
--
-- For CS F331 / CSCE A331 Spring 2018
-- Test Program for Module interpit
-- Used in Assignment 6, Exercise B

interpit = require "interpit"  -- Import interpit module


-- *********************************************
-- * YOU MAY WISH TO CHANGE THE FOLLOWING LINE *
-- *********************************************

EXIT_ON_FIRST_FAILURE = true
-- If EXIT_ON_FIRST_FAILURE is true, then this program exits after the
-- first failing test. If it is false, then this program executes all
-- tests, reporting success/failure for each.


-- *********************************************************************
-- Testing Package
-- *********************************************************************


tester = {}
tester.countTests = 0
tester.countPasses = 0

function tester.test(self, success, testName)
    self.countTests = self.countTests+1
    io.write("    Test: " .. testName .. " - ")
    if success then
        self.countPasses = self.countPasses+1
        io.write("passed")
    else
        io.write("********** FAILED **********")
    end
    io.write("\n")
end

function tester.allPassed(self)
    return self.countPasses == self.countTests
end


-- *********************************************************************
-- Utility Functions
-- *********************************************************************


function fail_exit()
    if EXIT_ON_FIRST_FAILURE then
        io.write("**************************************************\n")
        io.write("* This test program is configured to exit after  *\n")
        io.write("* the first failing test. To make it execute all *\n")
        io.write("* tests, reporting success/failure for each, set *\n")
        io.write("* variable                                       *\n")
        io.write("*                                                *\n")
        io.write("*   EXIT_ON_FIRST_FAILURE                        *\n")
        io.write("*                                                *\n")
        io.write("* to false, near the start of the test program.  *\n")
        io.write("**************************************************\n")

        -- Wait for user
        io.write("\nPress ENTER to quit ")
        io.read("*l")

        -- Terminate program
        os.exit(1)
    end
end


-- printTable
-- Given a table, prints it in (roughly) Lua literal notation. If
-- parameter is not a table, prints <not a table>.
function printTable(t)
    -- out
    -- Print parameter, surrounded by double quotes if it is a string,
    -- or simply an indication of its type, if it is not number, string,
    -- or boolean.
    local function out(p)
        if type(p) == "number" then
            io.write(p)
        elseif type(p) == "string" then
            io.write('"'..p..'"')
        elseif type(p) == "boolean" then
            if p then
                io.write("true")
            else
                io.write("false")
            end
        else
            io.write('<'..type(p)..'>')
        end
    end

    if type(t) ~= "table" then
        io.write("<not a table>")
    end

    io.write("{ ")
    local first = true  -- First iteration of loop?
    for k, v in pairs(t) do
        if first then
            first = false
        else
            io.write(", ")
        end
        io.write("[")
        out(k)
        io.write("]=")
        out(v)
    end
    io.write(" }")
end


-- printArray
-- Given a table, prints it in (roughly) Lua literal notation for an
-- array. If parameter is not a table, prints <not a table>.
function printArray(t)
    -- out
    -- Print parameter, surrounded by double quotes if it is a string.
    local function out(p)
        if type(p) == "string" then io.write('"') end
        io.write(p)
        if type(p) == "string" then io.write('"') end
    end

    if type(t) ~= "table" then
        io.write("<not a table>")
    end

    io.write("{ ")
    local first = true  -- First iteration of loop?
    for k, v in ipairs(t) do
        if first then
            first = false
        else
            io.write(", ")
        end
        out(v)
    end
    io.write(" }")
end


-- numKeys
-- Given a table, return the number of keys in it.
function numKeys(tab)
    local keycount = 0
    for k, v in pairs(tab) do
        keycount = keycount + 1
    end
    return keycount
end


-- tableEq
-- Compare equality of two tables.
-- Handles table values recursively. Does "==" on non-table values.
-- Uses function numKeys.
function tableEq(t1, t2)
    -- Both params are tables?
    if type(t1) ~= "table" or type(t2) ~= "table" then
        return false
    end

    if numKeys(t1) ~= numKeys(t2) then
        return false
    end

    for k, t1v in pairs(t1) do
        local t2v = t2[k]
        if type(t1v) == "table" and type(t2v) == "table" then
            if not tableEq(t1v, t2v) then
                return false
            end
        else
            if t1v ~= t2v then
                return false
            end
        end
    end

    return true
end


-- *********************************************************************
-- Definitions for This Test Program
-- *********************************************************************


-- Symbolic Constants for AST
-- Names differ from those in assignment, to avoid interference.
local STMTxLIST   = 1
local INPUTxSTMT  = 2
local PRINTxSTMT  = 3
local FUNCxSTMT   = 4
local CALLxFUNC   = 5
local IFxSTMT     = 6
local WHILExSTMT  = 7
local ASSNxSTMT   = 8
local CRxOUT      = 9
local STRLITxOUT  = 10
local BINxOP      = 11
local UNxOP       = 12
local NUMLITxVAL  = 13
local BOOLLITxVAL = 14
local SIMPLExVAR  = 15
local ARRAYxVAR   = 16


-- deepcopy
-- Returns deep copy of given value.
-- From http://lua-users.org/wiki/CopyTable
function deepcopy(orig)
    local orig_type = type(orig)
    local copy
    if orig_type == 'table' then
        copy = {}
        for orig_key, orig_value in next, orig, nil do
            copy[deepcopy(orig_key)] = deepcopy(orig_value)
        end
        setmetatable(copy, deepcopy(getmetatable(orig)))
    else -- number, string, boolean, etc
        copy = orig
    end
    return copy
end


-- isState
-- Return true if given value is properly formatted Dugong state table,
-- false otherwise.
function isState(tab)
    -- Is table?
    if type(tab) ~= "table" then
        return false
    end

    -- Has exactly 3 keys?
    if numKeys(tab) ~= 3 then
        return false
    end

    -- Has f, v, a keys?
    if tab.f == nil or tab.v == nil or tab.a == nil then
        return false
    end

    -- f, v, a keys are tables?
    if type(tab.f) ~= "table"
      or type(tab.v) ~= "table"
      or type(tab.a) ~= "table" then
        return false
    end

    -- All items in f are string:table
    -- String begins with "[_A-Za-z]"
    for k, v in pairs(tab.f) do
        if type(k) ~= "string" or type(v) ~= "table" then
            return false
        end
        if k:sub(1,1) ~= "_"
           and (k:sub(1,1) < "A" or k:sub(1,1) > "Z")
           and (k:sub(1,1) < "a" or k:sub(1,1) > "z") then
            return false
        end
    end

    -- All items in v are string:number
    -- String begins with "[_A-Za-z]"
    for k, v in pairs(tab.v) do
        if type(k) ~= "string" or type(v) ~= "number" then
            return false
        end
        if k:sub(1,1) ~= "_"
           and (k:sub(1,1) < "A" or k:sub(1,1) > "Z")
           and (k:sub(1,1) < "a" or k:sub(1,1) > "z") then
            return false
        end
    end

    -- All items in a are string:table
    -- String begins with "[_A-Za-z]"
    -- All items in values in a are number:number
    for k, v in pairs(tab.a) do
        if type(k) ~= "string" or type(v) ~= "table" then
            return false
        end
        if k:sub(1,1) ~= "_"
           and (k:sub(1,1) < "A" or k:sub(1,1) > "Z")
           and (k:sub(1,1) < "a" or k:sub(1,1) > "z") then
            return false
        end
        for kk, vv in pairs(v) do
            if type(kk) ~= "number" or type(vv) ~= "number" then
                return false
            end
        end
    end

    return true
end


-- checkInterp
-- Given tester object, AST, array of input strings, input state, array
-- of expected output strings, expected output state, and string giving
-- the name of the test. Calls interpit.interp and checks output strings
-- & state. Prints result. If test fails and EXIT_ON_FIRST_FAILURE is
-- true, then print detailed results and exit program.
function checkInterp(t, ast,
                     input, statein,
                     expoutput, expstateout,
                     testName)
    -- Error flags
    local err_incallparam = false
    local err_outcallnil = false
    local err_outcallnonstr = false

    local incount = 0
    local function incall(param)
        if param ~= nil then
            err_incallparam = true
        end
        incount = incount + 1
        if incount <= #input then
            return input[incount]
        else
            return ""
        end
    end

    local output = {}
    local function outcall(str)
        if type(str) == "string" then
            table.insert(output, str)
        elseif str == nil then
            err_outcallnil = true
            table.insert(output, "")
        else
            err_outcallnonstr = true
            table.insert(output, "")
        end
    end

    local stateout = interpit.interp(ast, statein, incall, outcall)

    local pass = true
    local msg = ""

    if incount > #input then
        pass = false
        msg = msg .. "Too many calls to incall\n"
    elseif incount < #input then
        pass = false
        msg = msg .. "Too few calls to incall\n"
    end

    if err_incallparam then
        pass = false
        msg = msg .. "incall called with parameter\n"
    end

    if #output > #expoutput then
        pass = false
        msg = msg .. "Too many calls to outcall\n"
    elseif #output < #expoutput then
        pass = false
        msg = msg .. "Too few calls to outcall\n"
    end

    if err_outcallnil then
        pass = false
        msg = msg .. "outcall called with nil or missing parameter\n"
    end
    if err_outcallnonstr then
        pass = false
        msg = msg .. "outcall called with non-string parameter\n"
    end

    if not tableEq(output, expoutput) then
        pass = false
        msg = msg .. "Output incorrect\n"
    end

    if isState(stateout) then
        if not tableEq(stateout, expstateout) then
            pass = false
            msg = msg .. "Returned state is incorrect\n"
        end
    else
        pass = false
        msg = msg .. "Returned state is not a Dugong state\n"
    end

    t:test(pass, testName)
    if pass or not EXIT_ON_FIRST_FAILURE then
        return
    end

    io.write("\n")
    io.write(msg)
    io.write("\n")
    fail_exit()
end


-- *********************************************************************
-- Test Suite Functions
-- *********************************************************************


function test_pre_written(t)
    io.write("Test Suite: programs that work with pre-written"
             .." interpit.lua\n")

    local ast, statein, expoutput, expstateout
    local emptystate = {v={}, a={}, f={}}

    -- Empty program
    ast = {STMTxLIST}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Empty program")

    -- Cr
    ast = {STMTxLIST, {PRINTxSTMT, {CRxOUT}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"\n"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "print cr")

    -- Two cr-statements
    ast = {STMTxLIST, {PRINTxSTMT, {CRxOUT}, {CRxOUT}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"\n", "\n"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "print cr;cr")

    -- Print: empty string
    ast = {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "''"}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {""}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print: empty string")

    -- Print: string, single-quoted
    ast = {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'abc'"}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"abc"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print: string, single-quoted")

    -- Print: string, double-quoted
    ast = {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, '"def"'}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"def"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print: string, double-quoted")

    -- Print: string + cr
    ast = {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'abc'"}, {CRxOUT}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"abc", "\n"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print: string + cr")

    -- Func, no call
    ast = {STMTxLIST, {FUNCxSTMT, "x",
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'abc'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={}, a={}, f={["x"]={STMTxLIST,
      {PRINTxSTMT, {STRLITxOUT, "'abc'"}}}}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Func, no call")

    -- Call, no func
    ast = {STMTxLIST, {CALLxFUNC, "x"}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Call, no func")

    -- Func with call (wrong name)
    ast = {STMTxLIST, {FUNCxSTMT, "x",
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'abc'"}}}},
      {CALLxFUNC, "y"}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={}, a={}, f={["x"]={STMTxLIST,
      {PRINTxSTMT, {STRLITxOUT, "'abc'"}}}}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Func with call (wrong name)")

    -- Func with call (right name)
    ast = {STMTxLIST, {FUNCxSTMT, "x",
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'abc'"}}}},
      {CALLxFUNC, "x"}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"abc"}
    expstateout = {v={}, a={}, f={["x"]={STMTxLIST,
      {PRINTxSTMT, {STRLITxOUT, "'abc'"}}}}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Func with call (right name)")

    -- Func defs func, no call
    ast = {STMTxLIST, {FUNCxSTMT, "x",
      {STMTxLIST, {FUNCxSTMT, "y", {STMTxLIST}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={}, a={}, f={["x"]={STMTxLIST,
      {FUNCxSTMT, "y", {STMTxLIST}}}}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Func defs func, no call")

    -- Func defs func, with call
    ast = {STMTxLIST, {FUNCxSTMT, "x",
      {STMTxLIST, {FUNCxSTMT, "y", {STMTxLIST}}}},
      {CALLxFUNC, "x"}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={}, a={}, f={["x"]={STMTxLIST,
      {FUNCxSTMT, "y", {STMTxLIST}}},
      ["y"]={STMTxLIST}}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Func defs func, with call")
end


function test_simple(t)
    io.write("Test Suite: simple programs\n")

    local ast, statein, expoutput, expstateout
    local emptystate = {v={}, a={}, f={}}

    -- Simple assignment: number
    ast = {STMTxLIST, {ASSNxSTMT, {SIMPLExVAR, "a"},
      {NUMLITxVAL, "42"}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={["a"]=42}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Simple assignment: number")

    -- Simple assignment: true
    ast = {STMTxLIST, {ASSNxSTMT, {SIMPLExVAR, "a"},
      {BOOLLITxVAL, "true"}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={["a"]=1}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Simple assignment: true")

    -- Simple assignment: false
    ast = {STMTxLIST, {ASSNxSTMT, {SIMPLExVAR, "a"},
      {BOOLLITxVAL, "false"}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={["a"]=0}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Simple assignment: false")

    -- Simple if #1
    ast = {STMTxLIST, {IFxSTMT, {NUMLITxVAL, "0"}, {STMTxLIST}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Simple if #1")

    -- Simple if #2
    ast = {STMTxLIST, {IFxSTMT, {NUMLITxVAL, "4"}, {STMTxLIST}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Simple if #2")

    -- Simple while
    ast = {STMTxLIST, {WHILExSTMT, {NUMLITxVAL, "0"}, {STMTxLIST}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Simple while")

   -- Simple input
    ast = {STMTxLIST, {INPUTxSTMT, {SIMPLExVAR, "b"}}}
    input = {"37"}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={["b"]=37}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Simple input")

    -- Print: number
    ast = {STMTxLIST, {PRINTxSTMT, {NUMLITxVAL, "28"}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"28"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print: number")

    -- Print: undefined variable
    ast = {STMTxLIST, {PRINTxSTMT, {SIMPLExVAR, "d"}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print: undefined variable")

    -- Set + print: variable
    ast = {STMTxLIST, {ASSNxSTMT, {SIMPLExVAR, "c"},
      {NUMLITxVAL, "57"}}, {PRINTxSTMT, {SIMPLExVAR, "c"}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"57"}
    expstateout = {v={["c"]=57}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Set + print: variable")

    -- Set + print: other variable
    ast = {STMTxLIST, {ASSNxSTMT, {SIMPLExVAR, "c"},
      {NUMLITxVAL, "57"}}, {PRINTxSTMT, {SIMPLExVAR, "d"}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = {v={["c"]=57}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Set + print: variable")

    -- Input + print: variable
    ast = {STMTxLIST, {INPUTxSTMT, {SIMPLExVAR, "c"}},
      {PRINTxSTMT, {SIMPLExVAR, "c"}}}
    input = {"12"}
    statein = deepcopy(emptystate)
    expoutput = {"12"}
    expstateout = {v={["c"]=12}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Input + print: variable")

    -- Input + print: other variable
    ast = {STMTxLIST, {INPUTxSTMT, {SIMPLExVAR, "c"}},
      {PRINTxSTMT, {SIMPLExVAR, "d"}}}
    input = {"24"}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = {v={["c"]=24}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Input + print: other variable")

    -- Set array
    ast = {STMTxLIST, {ASSNxSTMT,
      {ARRAYxVAR, "a", {NUMLITxVAL, "2"}},
      {NUMLITxVAL, "7"}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={}, a={["a"]={[2]=7}}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Set array")
end


function test_state(t)
    io.write("Test Suite: modified initial state\n")

    local ast, statein, expoutput, expstateout
    local emptystate = {v={}, a={}, f={}}

    -- Empty program
    ast = {STMTxLIST}
    input = {}
    statein = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    expoutput = {}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - empty program")

    -- Set simple var #1
    ast = {STMTxLIST, {ASSNxSTMT, {SIMPLExVAR, "a"}, {NUMLITxVAL, "3"}}}
    input = {}
    statein = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    expoutput = {}
    expstateout = {v={["a"]=3,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - set simple var #1")

    -- Set simple var #2
    ast = {STMTxLIST, {ASSNxSTMT, {SIMPLExVAR, "c"}, {NUMLITxVAL, "3"}}}
    input = {}
    statein = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    expoutput = {}
    expstateout = {v={["a"]=1,["b"]=2,["c"]=3},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - set simple var #2")

    -- Set array #1
    ast = {STMTxLIST, {ASSNxSTMT,
      {ARRAYxVAR, "b", {NUMLITxVAL, "2"}},
      {NUMLITxVAL, "9"}}}
    input = {}
    statein = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    expoutput = {}
    expstateout = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=9,[4]=3}}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - set array #1")

    -- Set array #2
    ast = {STMTxLIST, {ASSNxSTMT,
      {ARRAYxVAR, "b", {NUMLITxVAL, "-5"}},
      {NUMLITxVAL, "9"}}}
    input = {}
    statein = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    expoutput = {}
    expstateout = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3,[-5]=9}}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - set array #2")

    -- Set array #3
    ast = {STMTxLIST, {ASSNxSTMT,
      {ARRAYxVAR, "c", {NUMLITxVAL, "0"}},
      {NUMLITxVAL, "9"}}}
    input = {}
    statein = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    expoutput = {}
    expstateout = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3},["c"]={[0]=9}},
      f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - set array #3")

    -- Print simple var #1
    ast = {STMTxLIST, {PRINTxSTMT, {SIMPLExVAR, "a"}}}
    input = {}
    statein = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - Print simple var #1")

    -- Print simple var #2
    ast = {STMTxLIST, {PRINTxSTMT, {SIMPLExVAR, "c"}}}
    input = {}
    statein = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - Print simple var #2")

    -- Print array #1
    ast = {STMTxLIST, {PRINTxSTMT, {ARRAYxVAR, "a",
      {NUMLITxVAL, "4"}}}}
    input = {}
    statein = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    expoutput = {"7"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - Print array #1")

    -- Print array #2
    ast = {STMTxLIST, {PRINTxSTMT, {ARRAYxVAR, "a",
      {NUMLITxVAL, "8"}}}}
    input = {}
    statein = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - Print array #2")

    -- Print array #3
    ast = {STMTxLIST, {PRINTxSTMT, {ARRAYxVAR, "c",
      {NUMLITxVAL, "8"}}}}
    input = {}
    statein = {v={["a"]=1,["b"]=2},
      a={["a"]={[2]=3,[4]=7},["b"]={[2]=7,[4]=3}}, f={}}
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - Print array #3")

    -- Print-set-print-input-print
    ast = {STMTxLIST,
      {PRINTxSTMT, {SIMPLExVAR, "abc"}},
      {ASSNxSTMT, {SIMPLExVAR, "abc"}, {NUMLITxVAL, "55"}},
      {PRINTxSTMT, {SIMPLExVAR, "abc"}},
      {INPUTxSTMT, {SIMPLExVAR, "abc"}},
      {PRINTxSTMT, {SIMPLExVAR, "abc"}}}
    input = {"66"}
    statein = {v={["abc"]=44}, a={}, f={}}
    expoutput = {"44", "55", "66"}
    expstateout = {v={["abc"]=66}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - Print-set-print-input-print")

    -- Call func
    ast = {STMTxLIST, {CALLxFUNC, "q"}}
    input = {}
    statein = {v={}, a={}, f={["q"]=
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'x'"}}}
    }}
    expoutput = {"x"}
    expstateout = {v={}, a={}, f={["q"]=
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'x'"}}}
    }}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Modified initial state - Function")
end


function test_expr(t)
    io.write("Test Suite: expressions\n")

    local ast, statein, expoutput, expstateout
    local emptystate = {v={}, a={}, f={}}

    -- Print unary +
    ast = {STMTxLIST, {PRINTxSTMT,
      {{UNxOP, "+"}, {NUMLITxVAL, "5"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"5"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print unary +")

    -- Print unary -
    ast = {STMTxLIST, {PRINTxSTMT,
      {{UNxOP, "-"}, {NUMLITxVAL, "5"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"-5"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print unary -")

    -- Print ! #1
    ast = {STMTxLIST, {PRINTxSTMT,
      {{UNxOP, "!"}, {NUMLITxVAL, "5"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print ! #1")

    -- Print ! #2
    ast = {STMTxLIST, {PRINTxSTMT,
      {{UNxOP, "!"}, {NUMLITxVAL, "0"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print ! #2")

    -- Print binary +
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "+"}, {NUMLITxVAL, "5"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"7"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print binary +")

    -- Print binary -
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "-"}, {NUMLITxVAL, "5"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"3"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print binary -")

    -- Print *
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "*"}, {NUMLITxVAL, "5"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"10"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print *")

    -- Print /
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "/"}, {NUMLITxVAL, "5"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"2"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print /")

    -- Print / (div by zero)
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "/"}, {NUMLITxVAL, "5"}, {NUMLITxVAL, "0"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print / (div by zero)")

    -- Print %
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "%"}, {NUMLITxVAL, "5"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print %")

    -- Print % (div by zero)
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "%"}, {NUMLITxVAL, "5"}, {NUMLITxVAL, "0"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print % (div by zero)")

    -- Print == #1
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "=="}, {NUMLITxVAL, "5"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print == #1")

    -- Print == #2
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "=="}, {NUMLITxVAL, "5"}, {NUMLITxVAL, "5"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print == #2")

    -- Print != #1
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "!="}, {NUMLITxVAL, "5"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print != #1")

    -- Print != #2
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "!="}, {NUMLITxVAL, "5"}, {NUMLITxVAL, "5"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print != #2")

    -- Print < #1
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "<"}, {NUMLITxVAL, "1"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print < #1")

    -- Print < #2
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "<"}, {NUMLITxVAL, "2"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print < #2")

    -- Print < #3
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "<"}, {NUMLITxVAL, "3"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print < #3")

    -- Print <= #1
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "<="}, {NUMLITxVAL, "1"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print <= #1")

    -- Print <= #2
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "<="}, {NUMLITxVAL, "2"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print <= #2")

    -- Print <= #3
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "<="}, {NUMLITxVAL, "3"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print <= #3")

    -- Print > #1
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, ">"}, {NUMLITxVAL, "1"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print > #1")

    -- Print > #2
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, ">"}, {NUMLITxVAL, "2"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print > #2")

    -- Print > #3
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, ">"}, {NUMLITxVAL, "3"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print > #3")

    -- Print >= #1
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, ">="}, {NUMLITxVAL, "1"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print >= #1")

    -- Print >= #2
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, ">="}, {NUMLITxVAL, "2"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print >= #2")

    -- Print >= #3
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, ">="}, {NUMLITxVAL, "3"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print >= #3")

    -- Print && #1
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "&&"}, {NUMLITxVAL, "2"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print && #1")

    -- Print && #2
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "&&"}, {NUMLITxVAL, "2"}, {NUMLITxVAL, "0"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print && #2")

    -- Print && #3
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "&&"}, {NUMLITxVAL, "0"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print && #3")

    -- Print && #4
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "&&"}, {NUMLITxVAL, "0"}, {NUMLITxVAL, "0"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print && #4")

    -- Print || #1
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "||"}, {NUMLITxVAL, "2"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print || #1")

    -- Print || #2
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "||"}, {NUMLITxVAL, "2"}, {NUMLITxVAL, "0"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print || #2")

    -- Print || #3
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "||"}, {NUMLITxVAL, "0"}, {NUMLITxVAL, "2"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"1"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print || #3")

    -- Print || #4
    ast = {STMTxLIST, {PRINTxSTMT,
      {{BINxOP, "||"}, {NUMLITxVAL, "0"}, {NUMLITxVAL, "0"}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Print || #4")

    -- Longer expression
    ast =
      {STMTxLIST,
        {PRINTxSTMT,
          {{UNxOP, "-"},
            {{BINxOP, "-"},
              {{BINxOP, "=="}, {SIMPLExVAR, "x"}, {NUMLITxVAL, "3"}},
              {{BINxOP, "*"},
                {{BINxOP, "+"},
                  {NUMLITxVAL, "8"},
                  {BOOLLITxVAL, "true"}},
                {{UNxOP, "+"}, {SIMPLExVAR, "y"}}
              }
            }
          }
        }
      }
    input = {}
    statein = {v={["x"]=3, ["y"]=5}, a={}, f={}}
    expoutput = {"44"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Longer expression")
end


function test_intconv(t)
    io.write("Test Suite: integer conversion\n")

    local ast, statein, expoutput, expstateout
    local emptystate = {v={}, a={}, f={}}

    -- Numeric literal #1
    ast =
      {STMTxLIST,
        {ASSNxSTMT, {SIMPLExVAR, "n"}, {NUMLITxVAL, "5.4"}}
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={["n"]=5}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Integer conversion - numeric literal #1")

    -- Numeric literal #2
    ast =
      {STMTxLIST,
        {ASSNxSTMT, {SIMPLExVAR, "n"}, {NUMLITxVAL, "-7.4"}}
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={["n"]=-7}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Integer conversion - numeric literal #2")

    -- Numeric literal #3
    ast =
      {STMTxLIST,
        {ASSNxSTMT, {SIMPLExVAR, "n"}, {NUMLITxVAL, "5.74e1"}}
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={["n"]=57}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Integer conversion - numeric literal #3")

    -- Input
    ast =
      {STMTxLIST,
        {INPUTxSTMT, {SIMPLExVAR, "n"}}
      }
    input = {"2.9"}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = {v={["n"]=2}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Integer conversion - input")

    -- Division + multiplication #1
    ast =
      {STMTxLIST,
        {PRINTxSTMT,
          {{BINxOP, "*"},
            {{BINxOP, "/"}, {NUMLITxVAL, "10"}, {NUMLITxVAL, "3"}},
            {NUMLITxVAL, "3"}
          }
        }
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"9"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Integer conversion - division + multiplication #1")

    -- Division + multiplication #2
    ast =
      {STMTxLIST,
        {PRINTxSTMT,
          {{BINxOP, "*"},
            {{BINxOP, "/"}, {NUMLITxVAL, "-3"}, {NUMLITxVAL, "2"}},
            {NUMLITxVAL, "2"}
          }
        }
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"-2"}
    expstateout = deepcopy(statein)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Integer conversion - division + multiplication #2")
end


function test_if(t)
    io.write("Test Suite: if-statements\n")

    local ast, statein, expoutput, expstateout
    local emptystate = {v={}, a={}, f={}}

    -- If #1
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "4"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"a"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If #1")

    -- If #2
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If #1")

    -- If-else #1
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "5"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"a"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If-else #1")

    -- If-else #2
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"b"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If-else #2")

    -- If-elseif #1
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "6"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
      {NUMLITxVAL, "7"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"a"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If-elseif #1")

    -- If-elseif #2
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
      {NUMLITxVAL, "7"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"b"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If-elseif #2")

    -- If-elseif #3
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If-elseif #3")

    -- If-elseif-else #1
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "6"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
      {NUMLITxVAL, "7"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'c'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"a"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If-elseif-else #1")

    -- If-elseif-else #2
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
      {NUMLITxVAL, "7"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'c'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"b"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If-elseif-else #2")

    -- If-elseif-else #3
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'c'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"c"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If-elseif-else #3")

    -- If-elseif*-else #1
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "8"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'c'"}}},
      {NUMLITxVAL, "9"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'d'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'e'"}}},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'f'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"a"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If-elseif*-else #1")

    -- If-elseif*-else #2
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'c'"}}},
      {NUMLITxVAL, "9"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'d'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'e'"}}},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'f'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"d"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If-elseif*-else #2")

    -- If-elseif*-else #3
    ast = {STMTxLIST, {IFxSTMT,
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'c'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'d'"}}},
      {NUMLITxVAL, "0"},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'e'"}}},
      {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'f'"}}}}}
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"f"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "If-elseif*-else #3")

    -- Nested if-else #1
    ast =
      {STMTxLIST,
        {IFxSTMT,
          {NUMLITxVAL, "1"},
          {STMTxLIST,
            {IFxSTMT,
              {NUMLITxVAL, "1"},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}}
            }
          },
          {STMTxLIST,
            {IFxSTMT,
              {NUMLITxVAL, "1"},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'c'"}}},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'d'"}}}
            }
          }
        }
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"a"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Nested if-else #1")

    -- Nested if-else #2
    ast =
      {STMTxLIST,
        {IFxSTMT,
          {NUMLITxVAL, "1"},
          {STMTxLIST,
            {IFxSTMT,
              {NUMLITxVAL, "0"},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}}
            }
          },
          {STMTxLIST,
            {IFxSTMT,
              {NUMLITxVAL, "0"},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'c'"}}},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'d'"}}}
            }
          }
        }
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"b"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Nested if-else #2")

    -- Nested if-else #3
    ast =
      {STMTxLIST,
        {IFxSTMT,
          {NUMLITxVAL, "0"},
          {STMTxLIST,
            {IFxSTMT,
              {NUMLITxVAL, "1"},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}}
            }
          },
          {STMTxLIST,
            {IFxSTMT,
              {NUMLITxVAL, "1"},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'c'"}}},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'d'"}}}
            }
          }
        }
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"c"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Nested if-else #3")

    -- Nested if-else #4
    ast =
      {STMTxLIST,
        {IFxSTMT,
          {NUMLITxVAL, "0"},
          {STMTxLIST,
            {IFxSTMT,
              {NUMLITxVAL, "0"},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'a'"}}},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'b'"}}}
            }
          },
          {STMTxLIST,
            {IFxSTMT,
              {NUMLITxVAL, "0"},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'c'"}}},
              {STMTxLIST, {PRINTxSTMT, {STRLITxOUT, "'d'"}}}
            }
          }
        }
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"d"}
    expstateout = deepcopy(emptystate)
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Nested if-else #4")
end


function test_while(t)
    io.write("Test Suite: while-loops\n")

    local ast, statein, expoutput, expstateout
    local emptystate = {v={}, a={}, f={}}

    -- While loop - counted
    ast =
      {STMTxLIST,
        {ASSNxSTMT, {SIMPLExVAR, "i"}, {NUMLITxVAL, "0"}},
        {WHILExSTMT,
          {{BINxOP, "<"}, {SIMPLExVAR, "i"}, {NUMLITxVAL, "7"}},
          {STMTxLIST,
            {PRINTxSTMT,
              {{BINxOP, "*"}, {SIMPLExVAR, "i"}, {SIMPLExVAR, "i"}}
            },
            {ASSNxSTMT,
              {SIMPLExVAR, "i"},
              {{BINxOP, "+"}, {SIMPLExVAR, "i"}, {NUMLITxVAL, "1"}}
            }
          }
        }
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"0", "1", "4", "9", "16", "25", "36"}
    expstateout = {v={["i"]=7},a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "While loop - counted")

    -- While loop - input with sentinel
    ast =
      {STMTxLIST,
        {ASSNxSTMT, {SIMPLExVAR, "notdone"}, {NUMLITxVAL, "1"}},
        {WHILExSTMT,
          {SIMPLExVAR, "notdone"},
          {STMTxLIST,
            {INPUTxSTMT, {SIMPLExVAR, "n"}},
            {IFxSTMT,
              {{BINxOP, "=="}, {SIMPLExVAR, "n"}, {NUMLITxVAL, "99"}},
              {STMTxLIST,
                {ASSNxSTMT, {SIMPLExVAR, "notdone"}, {NUMLITxVAL, "0"}}
              },
              {STMTxLIST,
                {PRINTxSTMT, {SIMPLExVAR, "n"}, {CRxOUT}}
              }
            }
          }
        },
        {PRINTxSTMT, {STRLITxOUT, "'Bye!'"}, {CRxOUT}}
      }
    input = {"1", "8", "-17", "13.5", "99"}
    statein = deepcopy(emptystate)
    expoutput = {"1", "\n", "8", "\n", "-17", "\n", "13", "\n", "Bye!",
      "\n"}
    expstateout = {v={["notdone"]=0, ["n"]=99}, a={}, f={}}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "While loop - input with sentinel")
end


function test_func(t)
    io.write("Test Suite: fancy functions\n")

    local ast, statein, expoutput, expstateout
    local emptystate = {v={}, a={}, f={}}

    -- Returning a value
    ast =
      {STMTxLIST,
        {FUNCxSTMT, "sq",
          {STMTxLIST,
            {ASSNxSTMT,
              {SIMPLExVAR, "return"},
              {{BINxOP, "*"}, {SIMPLExVAR, "a"}, {SIMPLExVAR, "a"}}
            }
          }
        },
        {ASSNxSTMT,
          {SIMPLExVAR, "a"},
          {NUMLITxVAL, "7"}
        },
        {PRINTxSTMT,
          {CALLxFUNC, "sq"},
          {CRxOUT}
        }
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"49","\n"}
    expstateout = {v={["a"]=7,["return"]=49}, a={}, f={["sq"]=
      {STMTxLIST, {ASSNxSTMT, {SIMPLExVAR, "return"}, {{BINxOP, "*"},
      {SIMPLExVAR, "a"}, {SIMPLExVAR, "a"}}}}
    }}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Returning a value")

    -- Recursion
    ast =
      {STMTxLIST,
        {FUNCxSTMT, "x",
          {STMTxLIST,
            {PRINTxSTMT, {SIMPLExVAR, "c"}},
            {ASSNxSTMT,
              {SIMPLExVAR, "c"},
              {{BINxOP, "-"}, {SIMPLExVAR, "c"}, {NUMLITxVAL, "1"}}
            },
            {IFxSTMT,
              {{BINxOP, ">"}, {SIMPLExVAR, "c"}, {NUMLITxVAL, "0"}},
              {STMTxLIST, {CALLxFUNC, "x"}}
            }
          }
        },
        {ASSNxSTMT, {SIMPLExVAR, "c"}, {NUMLITxVAL, "3"}},
        {CALLxFUNC, "x"}
      }
    input = {}
    statein = deepcopy(emptystate)
    expoutput = {"3", "2", "1"}
    expstateout = {v={["c"]=0}, a={}, f={["x"]=
      {STMTxLIST, {PRINTxSTMT, {SIMPLExVAR, "c"}},
      {ASSNxSTMT, {SIMPLExVAR, "c"},
      {{BINxOP, "-"}, {SIMPLExVAR, "c"}, {NUMLITxVAL, "1"}}},
      {IFxSTMT, {{BINxOP, ">"}, {SIMPLExVAR, "c"}, {NUMLITxVAL, "0"}},
      {STMTxLIST, {CALLxFUNC, "x"}}}}
    }}
    checkInterp(t, ast, input, statein, expoutput, expstateout,
      "Recursion")
end


function test_interpit(t)
    io.write("TEST SUITES FOR MODULE interpit\n")
    test_pre_written(t)
    test_simple(t)
    test_state(t)
    test_expr(t)
    test_intconv(t)
    test_if(t)
    test_while(t)
    test_func(t)
end


-- *********************************************************************
-- Main Program
-- *********************************************************************


test_interpit(tester)
io.write("\n")
if tester:allPassed() then
    io.write("All tests successful\n")
else
    io.write("Tests ********** UNSUCCESSFUL **********\n")
    io.write("\n")
    io.write("**************************************************\n")
    io.write("* This test program is configured to execute all *\n")
    io.write("* tests, reporting success/failure for each. To  *\n")
    io.write("* make it exit after the first failing test, set *\n")
    io.write("* variable                                       *\n")
    io.write("*                                                *\n")
    io.write("*   EXIT_ON_FIRST_FAILURE                        *\n")
    io.write("*                                                *\n")
    io.write("* to true, near the start of the test program.   *\n")
    io.write("**************************************************\n")
end

-- Wait for user
io.write("\nPress ENTER to quit ")
io.read("*l")

