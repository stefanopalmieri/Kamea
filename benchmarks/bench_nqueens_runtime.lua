--- bench_nqueens_runtime.lua — LuaJIT N-Queens with argv input
--- Run: luajit benchmarks/bench_nqueens_runtime.lua 8

local N = tonumber(arg[1])

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

-- Warmup
nqueens(N)

-- Bench
local iters = 10000
local t0 = os.clock()
local result = 0
for _ = 1, iters do
    result = nqueens(N)
end
local t1 = os.clock()
local per_iter_us = (t1 - t0) / iters * 1e6
io.write(string.format("N-Queens(%d):        %.1f µs/iter (%d iters, result=%d)\n",
    N, per_iter_us, iters, result))
