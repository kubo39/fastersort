import std.algorithm.mutation : SwapStrategy;
import std.functional : binaryFun;
import std.range;

template MergeSortImpl(alias pred, R)
{
    import core.stdc.string : memcpy;

    static assert(isRandomAccessRange!R);
    static assert(hasLength!R);
    static assert(hasSlicing!R);
    static assert(hasAssignableElements!R);

    alias T = ElementType!R;

    alias less = binaryFun!pred;
    alias greater = (a, b) => less(b, a);
    alias greaterEqual = (a, b) => !less(a, b);
    alias lessEqual = (a, b) => !less(b, a);

    // Insert r.first into pre-sorted r[1 .. $].
    void insertHead()(R r)
    {
        if (r.length >= 2 && less(r[1], r[0]))
        {
            // Copy the first element.
            const tmp = r[0];
            auto dest = &r[1];
            memcpy(&r[0], dest, T.sizeof);
            // Iterate until the right place for it is found.
            foreach (i; 2 .. r.length)
            {
                if (greaterEqual(r[i], tmp))
                    break;
                memcpy(&r[i - 1], &r[i], T.sizeof);
                dest = &r[i];
            }
            // Copies tmp to dest.
            memcpy(dest, &tmp, T.sizeof);
        }
    }

    // Merge r[0 .. mid] and r[mid .. $] using buf as temporary storage.
    void merge()(R r, size_t mid, T* buf)
    {
        static assert(T.sizeof != 0);

        immutable n = r.length;
        auto arrMid = r.ptr + mid;
        auto arrEnd = r.ptr + n;

        struct MergeHole
        {
            T* start;
            T* end;
            T* dest;
        }
        MergeHole hole;

        T* getAndIncrement(T** ptr)
        {
            auto old = *ptr;
            ++*ptr;
            return old;
        }

        T* decrementAndGet(T** ptr)
        {
            return --*ptr;
        }

        // Copies the shorter run into buf.
        if (mid <= n - mid)
        {
            // The left run is shorter.
            // Copy arr[0 .. mid] into buf.
            memcpy(buf, r.ptr, T.sizeof * mid);
            hole = MergeHole(buf, buf + mid, r.ptr);

            auto left = &hole.start;
            auto right = arrMid;
            auto out_ = &hole.dest;

            while (*left < hole.end && right < arrEnd)
            {
                // Consume lesser side.
                const toCopy = less(*right, **left)
                    ? getAndIncrement(&right)
                    : getAndIncrement(left);
                memcpy(getAndIncrement(out_), toCopy, T.sizeof);
            }
        }
        else
        {
            // The right run is shorter.
            // Copy r[mid .. $] into buf.
            memcpy(buf, arrMid, T.sizeof * (n - mid));
            hole = MergeHole(buf, buf + (n - mid), arrMid);

            auto left = &hole.dest;
            auto right = &hole.end;
            auto out_ = arrEnd;

            while (r.ptr < *left && buf < *right)
            {
                const toCopy = less(*(*right-1), *(*left-1))
                    ? decrementAndGet(left)
                    : decrementAndGet(right);
                memcpy(decrementAndGet(&out_), toCopy, T.sizeof);
            }
        }
        memcpy(hole.dest, hole.start, (hole.end - hole.start) * T.sizeof);
    }

    void sort()(R r)
    {
        import std.algorithm : reverse, remove;
        import std.array : uninitializedArray;

        enum MINIMUL_MERGE = 20;
        enum MIN_RUN = 10;

        if (T.sizeof == 0)
            return;

        immutable n = r.length;

        if (n <= MINIMUL_MERGE)
        {
            // insertion sort.
            if (n >= 2)
                foreach_reverse (i; 0 .. n-1)
                    insertHead(r[i .. $]);
            return;
        }

        // Allocate temporary buffer to copy shorter run.
        // Which will always have length at most n / 2.
        auto buf = uninitializedArray!(T[])(n / 2);

        struct Run
        {
            size_t start;
            size_t len;
        }

        Run[] runs = [];
        size_t end = n;

        while (end > 0)
        {
            auto start = end - 1;
            if (start > 0)
            {
                start--;
                if (less(r[start+1], r[start]))
                {
                    while (start > 0 && less(r[start], r[start-1]))
                        start--;
                    r[start .. end].reverse();
                }
                else
                    while (start > 0 && greaterEqual(r[start], r[start-1]))
                        start--;
            }

            // Optimization:
            // Insert some more elements into the run
            // if it's too short.
            while (start > 0 && end - start < MIN_RUN)
            {
                start--;
                insertHead(r[start .. end]);
            }

            runs ~= Run(start, end - start);
            end = start;

            // Examines the stack of runs and identifies the next pair of runs to merge.
            size_t collapse(Run[] runs)
            {
                const n = runs.length;
                if (n >= 2 && (runs[n-1].start == 0 ||
                               runs[n-2].len <= runs[n-1].len ||
                               (n >= 3 && runs[n-3].len <= runs[n-2].len + runs[n-1].len) ||
                               (n >= 4 && runs[n-4].len <= runs[n-3].len + runs[n-2].len)))
                {
                    if (n >= 3 && runs[n-3].len < runs[n-1].len)
                        return n-3;
                    else
                        return n-2;
                }
                else
                    return size_t.max;
            }

            while (true)
            {
                const i = collapse(runs);
                if (i == size_t.max)
                    break;

                const left = runs[i+1];
                const right = runs[i];

                merge(r[left.start .. right.start + right.len], left.len, buf.ptr);
                runs[i] = Run(left.start, left.len + right.len);
                runs = runs.remove(i+1);
            }
        }

        import std.format : format;
        assert(runs.length == 1 && runs[0].start == 0 && runs[0].len == n, format("%s", runs));
    }
}

// Stable sort, that is faster than stdlib's Tim sort.
// This algorithm is based on Python's object sort and Rust's std::sort.
auto fastersort(alias less = "a < b", SwapStrategy ss = SwapStrategy.stable,
                Range)(Range r)
    if ((ss != SwapStrategy.unstable && hasAssignableElements!Range) &&
        isRandomAccessRange!Range &&
        hasSlicing!Range &&
        hasLength!Range)
{
    alias lessFun = binaryFun!less;
    alias LessRet = typeof(lessFun(r.front, r.front));
    static if (is(LessRet == bool))
    {
        static if (ss == SwapStrategy.stable)
            MergeSortImpl!(lessFun, Range).sort(r);
        else static assert (false);
    }
    else static assert (false);
}

unittest
{
    import std.algorithm : map;
    import std.array : array;
    import std.format : format;
    import std.random : rndGen, uniform;
    import std.range : take;

    // simply.
    {
        import std.algorithm : /*sort,*/ SwapStrategy, isSorted;

        foreach (_; 0 .. 1000)
        {
            auto len = uniform(0, size_t.max) % 1000 + 1;
            auto limit = uniform(0, ulong.max) % 1000 + 1;
            auto a = rndGen()
                .map!(a => a % limit)
                .take(len)
                .array;
            a.fastersort();
            assert(a.isSorted, format("%s", a));
            a.fastersort!"a > b"();
            assert(a.isSorted!"a > b", format("%s", a));
        }
    }
}

void main()
{
    import std.algorithm : map;
    import std.array : array;
    import std.conv : to;
    import std.format : format;
    import std.random : rndGen, uniform;
    import std.range : take;

    import std.algorithm : sort, SwapStrategy, isSorted;

    ulong[] genRandom(ulong len)
    {
        return rndGen().map!(to!ulong).take(len).array;
    }

    void stdsort() { genRandom(10_000).sort!("a < b", SwapStrategy.stable); }
    void newersort() { genRandom(10_000).fastersort!"a < b"; }

    import core.time;
    import std.datetime.stopwatch : benchmark;
    import std.stdio;

    auto r = benchmark!(stdsort, newersort)(100);
    writeln("stdsort");
    r[0].to!Duration.writeln;
    writeln("newersort");
    r[1].to!Duration.writeln;

    // (dmd-2.078.0)$ rdmd fastersort.d
    // stdsort
    // 431 ms, 172 μs, and 6 hnsecs
    // newersort
    // 290 ms, 905 μs, and 3 hnsecs
}
