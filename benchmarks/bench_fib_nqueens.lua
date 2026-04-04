--- bench_fib_nqueens.lua — LuaJIT benchmark matching Psi-Lisp fib + nqueens
--- Run: luajit benchmarks/bench_fib_nqueens.lua

local get_time = os.clock

--- Counter arithmetic ---

local function fib(n)
    if n < 2 then return n end
    return fib(n - 1) + fib(n - 2)
end

local function fib_iter(n)
    local a, b = 0, 1
    for _ = 1, n do
        a, b = b, a + b
    end
    return a
end

local function fact(n)
    if n == 0 then return 1 end
    return n * fact(n - 1)
end

local function power(base, exp)
    if exp == 0 then return 1 end
    return base * power(base, exp - 1)
end

local function my_gcd(a, b)
    if b == 0 then return a end
    return my_gcd(b, a % b)
end

local function counter_arith()
    return fib(8) + fib_iter(30) + fact(10) + power(2, 10) + my_gcd(100, 75)
end

--- N-Queens(8) ---

-- Lists as tables: {val, next} or nil for empty
local function cons(x, lst) return {x, lst} end
local function car(lst) return lst[1] end
local function cdr(lst) return lst[2] end

local abs = math.abs

local function safe_p(queen, dist, placed)
    if placed == nil then return true end
    local q = car(placed)
    if queen == q then return false end
    if abs(queen - q) == dist then return false end
    return safe_p(queen, dist + 1, cdr(placed))
end

local function nqueens_count(n, row, placed)
    if row == n then return 1 end
    return count_cols(n, 0, row, placed)
end

function count_cols(n, col, row, placed)
    if col == n then return 0 end
    local s = 0
    if safe_p(col, 1, placed) then
        s = nqueens_count(n, row + 1, cons(col, placed))
    end
    return s + count_cols(n, col + 1, row, placed)
end

local function nqueens(n)
    return nqueens_count(n, 0, nil)
end

--- Timing ---

-- Warmup
counter_arith()
nqueens(8)

-- Bench counter arithmetic
local iters = 1000000
local t0 = get_time()
local result = 0
for _ = 1, iters do
    result = counter_arith()
end
local t1 = get_time()
local per_iter_us = (t1 - t0) / iters * 1e6
io.write(string.format("Counter arithmetic: %.3f µs/iter (%d iters, result=%d)\n",
    per_iter_us, iters, result))

-- Bench nqueens
iters = 10000
t0 = get_time()
result = 0
for _ = 1, iters do
    result = nqueens(8)
end
t1 = get_time()
per_iter_us = (t1 - t0) / iters * 1e6
io.write(string.format("N-Queens(8):        %.1f µs/iter (%d iters, result=%d)\n",
    per_iter_us, iters, result))
