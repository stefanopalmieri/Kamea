--- bench_counter_runtime.lua — LuaJIT counter arithmetic with argv inputs
--- Run: luajit benchmarks/bench_counter_runtime.lua 8 30 10 2 10 100 75

local fib_n    = tonumber(arg[1])
local iter_n   = tonumber(arg[2])
local fact_n   = tonumber(arg[3])
local pow_base = tonumber(arg[4])
local pow_exp  = tonumber(arg[5])
local gcd_a    = tonumber(arg[6])
local gcd_b    = tonumber(arg[7])

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
    return fib(fib_n) + fib_iter(iter_n) + fact(fact_n) +
           power(pow_base, pow_exp) + my_gcd(gcd_a, gcd_b)
end

-- Warmup
counter_arith()

-- Bench
local iters = 1000000
local t0 = os.clock()
local result = 0
for _ = 1, iters do
    result = counter_arith()
end
local t1 = os.clock()
local per_iter_us = (t1 - t0) / iters * 1e6
io.write(string.format("Counter arithmetic: %.3f µs/iter (%d iters, result=%d)\n",
    per_iter_us, iters, result))
