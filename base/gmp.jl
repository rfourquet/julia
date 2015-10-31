# This file is a part of Julia. License is MIT: http://julialang.org/license

module GMP

export BigInt

import Base: *, +, -, /, <, <<, >>, >>>, <=, ==, >, >=, ^, (~), (&), (|), ($),
             binomial, cmp, convert, div, divrem, factorial, fld, gcd, gcdx, lcm, mod,
             ndigits, promote_rule, rem, show, isqrt, string, isprime, powermod,
             sum, trailing_zeros, trailing_ones, count_ones, base, tryparse_internal,
             bin, oct, dec, hex, isequal, invmod, prevpow2, nextpow2, ndigits0z, widen, signed, unsafe_trunc, trunc

if Clong == Int32
    typealias ClongMax Union{Int8, Int16, Int32}
    typealias CulongMax Union{UInt8, UInt16, UInt32}
else
    typealias ClongMax Union{Int8, Int16, Int32, Int64}
    typealias CulongMax Union{UInt8, UInt16, UInt32, UInt64}
end
typealias CdoubleMax Union{Float16, Float32, Float64}

gmp_version() = VersionNumber(bytestring(unsafe_load(cglobal((:__gmp_version, :libgmp), Ptr{Cchar}))))
gmp_bits_per_limb() = Int(unsafe_load(cglobal((:__gmp_bits_per_limb, :libgmp), Cint)))

const GMP_VERSION = gmp_version()
const GMP_BITS_PER_LIMB = gmp_bits_per_limb()

# GMP's mp_limb_t is by default a typedef of `unsigned long`, but can also be configured to be either
# `unsigned int` or `unsigned long long int`. The correct unsigned type is here named Limb, and must
# be used whenever mp_limb_t is in the signature of ccall'ed GMP functions.
if GMP_BITS_PER_LIMB == 32
    typealias Limb UInt32
    typealias SLimbMax Union{Int8, Int16, Int32}
    typealias ULimbMax Union{UInt8, UInt16, UInt32}
elseif GMP_BITS_PER_LIMB == 64
    typealias Limb UInt64
    typealias SLimbMax Union{Int8, Int16, Int32, Int64}
    typealias ULimbMax Union{UInt8, UInt16, UInt32, UInt64}
else
    error("GMP: cannot determine the type mp_limb_t (__gmp_bits_per_limb == $GMP_BITS_PER_LIMB)")
end

typealias Limbs Vector{Limb}
typealias Size Clong
typealias _Size Cint # Cint in GMP, to save space

immutable BigInt <: Integer
    size::_Size
    d::Limbs
    #    BigInt(::Type{Val{:unsafe}}, size::Size, d::Limbs) = new(size, d % _Size)
#    BigInt(size=0) = new(size)
end

BigInt() = BigInt(0)

immutable MPZ1 <: Integer
    alloc::Cint
    size::Cint
    d::Ptr{Limb}
    MPZ1(z::BigInt) = new(length(z.d), z.size, pointer(z.d)) # should be immutable
end


type _MPZ <: Integer
    alloc::Cint
    size::Cint
    d::Ptr{Limb}
    function _MPZ()
        _z = new(zero(Cint), zero(Cint), C_NULL)
#        ccall((:__gmpz_init,:libgmp), Void, (Ptr{_MPZ},), &_z)
#        finalizer(b, _gmp_clear_func)
        return _z
    end
    _MPZ(z::BigInt) = new(length(z.d), z.size, pointer(z.d)) # should be immutable
end

typealias MPZ _MPZ

_finish(z::BigInt, _z::_MPZ) = z.size = _z.size

_reinit(_z::_MPZ) = ccall((:__gmpz_init,:libgmp), Void, (Ptr{_MPZ},), &_z)
_realloc2(_z::_MPZ, n) = ccall((:__gmpz_realloc2,:libgmp), Void, (Ptr{_MPZ}, Culong), &_z, n)

function _swap(_z::_MPZ, n)
    r = _z.d
    a = _z.alloc
    _z.d = pointer(n.d)
    _z.size = n.size
    _z.alloc = _z.size
    r, a
end
function _restore(_z::_MPZ, p, a)
    _z.d = p
    _z.size = 0
    _z.alloc = a
end

function _reinit2(_z::_MPZ)  #ccall((:__gmpz_init,:libgmp), Void, (Ptr{_MPZ},), &_z)
    _z.alloc = 0
    _z.size = 0
    _z.d = C_NULL
end

function BigInt(_z::_MPZ)
    # z = BigInt(_z.size, pointer_to_array(_z.d, _z.alloc, true))
    z = BigInt(_z.size, Limbs(abs(_z.size)))
    @inbounds for i in 1:length(z.d)
        z.d[i] = unsafe_load(_z.d, i)
    end

   # _reinit(_z)
    z
end

const _Z = _MPZ()
const _ZZ = _MPZ()
const _ZZZ = _MPZ()
const _Z0 = _MPZ()
const _Z1 = _MPZ()
@inline function wrapz(_z::_MPZ, n::BigInt)
    _z.size = n.size
    _z.alloc = length(n.d)
    _z.d = pointer(n.d)
    _z
end

_gmp_clear_func = C_NULL
_mpfr_clear_func = C_NULL

function __init__()
    try
        if gmp_version().major != GMP_VERSION.major || gmp_bits_per_limb() != GMP_BITS_PER_LIMB
            msg = gmp_bits_per_limb() != GMP_BITS_PER_LIMB ? error : warn
            msg(string("The dynamically loaded GMP library (version $(gmp_version()) with __gmp_bits_per_limb == $(gmp_bits_per_limb()))\n",
                       "does not correspond to the compile time version (version $GMP_VERSION with __gmp_bits_per_limb == $GMP_BITS_PER_LIMB).\n",
                       "Please rebuild Julia."))
        end

        global _gmp_clear_func = cglobal((:__gmpz_clear, :libgmp))
        global _mpfr_clear_func = cglobal((:mpfr_clear, :libmpfr))
        ccall((:__gmp_set_memory_functions, :libgmp), Void,
              (Ptr{Void},Ptr{Void},Ptr{Void}),
              cglobal(:jl_gc_counted_malloc),
              cglobal(:jl_gc_counted_realloc_with_old_size),
              cglobal(:jl_gc_counted_free))
    catch ex
        Base.showerror_nostdio(ex,
            "WARNING: Error during initialization of module GMP")
    end
end

widen(::Type{Int128})  = BigInt
widen(::Type{UInt128}) = BigInt
widen(::Type{BigInt})  = BigInt

signed(x::BigInt) = x

convert(::Type{BigInt}, x::BigInt) = x

function tryparse_internal(::Type{BigInt}, s::AbstractString, startpos::Int, endpos::Int, base::Int, raise::Bool)
    _n = Nullable{BigInt}()

    # don't make a copy in the common case where we are parsing a whole bytestring
    bstr = startpos == start(s) && endpos == endof(s) ? bytestring(s) : bytestring(SubString(s,startpos,endpos))

    sgn, base, i = Base.parseint_preamble(true,base,bstr,start(bstr),endof(bstr))
    if i == 0
        raise && throw(ArgumentError("premature end of integer: $(repr(bstr))"))
        return _n
    end
    if Base.containsnul(bstr)
        err = -1 # embedded NUL char (not handled correctly by GMP)
    else
        err = ccall((:__gmpz_set_str, :libgmp),
                    Int32, (Ptr{_MPZ}, Ptr{UInt8}, Int32),
                    &_Z, pointer(bstr)+(i-start(bstr)), base)
    end
    if err != 0
        raise && throw(ArgumentError("invalid BigInt: $(repr(bstr))"))
        return _n
    end
    z = BigInt(_Z)
    Nullable(sgn < 0 ? -z : z)

end

convert(::Type{BigInt}, x::SLimbMax) = BigInt(ifelse(x==0, 0, ifelse(x>0, 1, -1)),
                                              Limb[abs(x)])

convert(::Type{BigInt}, x::ULimbMax) = BigInt(_Size(x!=0), Limb[x])

convert(::Type{BigInt}, x::Bool) = BigInt(UInt(x))


function unsafe_trunc(::Type{BigInt}, x::Union{Float32,Float64})
    ccall((:__gmpz_set_d, :libgmp), Void, (Ptr{_MPZ}, Cdouble), &_Z, x)
    BigInt(_Z)
end

function convert(::Type{BigInt}, x::Union{Float32,Float64})
    isinteger(x) || throw(InexactError())
    unsafe_trunc(BigInt,x)
end

function trunc(::Type{BigInt}, x::Union{Float32,Float64})
    isfinite(x) || throw(InexactError())
    unsafe_trunc(BigInt,x)
end

convert(::Type{BigInt}, x::Float16) = BigInt(Float64(x))
convert(::Type{BigInt}, x::Float32) = BigInt(Float64(x))

function convert(::Type{BigInt}, x::Integer)
    if x < 0
        if typemin(Clong) <= x
            return BigInt(convert(Clong,x))
        end
        b = BigInt(0)
        shift = 0
        while x < -1
            b += BigInt(~UInt32(x&0xffffffff))<<shift
            x >>= 32
            shift += 32
        end
        return -b-1
    else
        if x <= typemax(Culong)
            return BigInt(convert(Culong,x))
        end
        b = BigInt(0)
        shift = 0
        while x > 0
            b += BigInt(UInt32(x&0xffffffff))<<shift
            x >>>= 32
            shift += 32
        end
        return b
    end
end


rem(x::BigInt, ::Type{Bool}) = ((x&1)!=0)
function rem{T<:Union{Unsigned,Signed}}(x::BigInt, ::Type{T})
    u = zero(T)
    @inbounds for l = 1:min(abs(x.size), cld(sizeof(T),sizeof(Limb)))
        u += (x.d[l]%T) << ((sizeof(Limb)<<3)*(l-1))
    end
    x.size < 0 ? -u : u
end

function convert{T<:Unsigned}(::Type{T}, x::BigInt)
    if sizeof(T) < sizeof(Limb)
        convert(T, convert(Limb,x))
    else
        0 <= x.size <= cld(sizeof(T),sizeof(Limb)) || throw(InexactError())
        x % T
    end
end

function convert{T<:Signed}(::Type{T}, x::BigInt)
    n = abs(x.size)
    if sizeof(T) < sizeof(Limb)
        SLimb = typeof(Signed(one(Limb)))
        convert(T, convert(SLimb, x))
    else
        0 <= n <= cld(sizeof(T),sizeof(Limb)) || throw(InexactError())
        y = x % T
        (x.size > 0) $ (y > 0) && throw(InexactError()) # catch overflow
        y
    end
end


function call(::Type{Float64}, n::BigInt, ::RoundingMode{:ToZero})
    ccall((:__gmpz_get_d, :libgmp), Float64, (Ptr{MPZ},), &MPZ(n))
end

function call{T<:Union{Float16,Float32}}(::Type{T}, n::BigInt, ::RoundingMode{:ToZero})
    T(Float64(n,RoundToZero),RoundToZero)
end

function call{T<:CdoubleMax}(::Type{T}, n::BigInt, ::RoundingMode{:Down})
    x = T(n,RoundToZero)
    x > n ? prevfloat(x) : x
end
function call{T<:CdoubleMax}(::Type{T}, n::BigInt, ::RoundingMode{:Up})
    x = T(n,RoundToZero)
    x < n ? nextfloat(x) : x
end

function call{T<:CdoubleMax}(::Type{T}, n::BigInt, ::RoundingMode{:Nearest})
    x = T(n,RoundToZero)
    if maxintfloat(T) <= abs(x) < T(Inf)
        r = n-BigInt(x)
        h = eps(x)/2
        if iseven(reinterpret(Unsigned,x)) # check if last bit is odd/even
            if r < -h
                return prevfloat(x)
            elseif r > h
                return nextfloat(x)
            end
        else
            if r <= -h
                return prevfloat(x)
            elseif r >= h
                return nextfloat(x)
            end
        end
    end
    x
end

convert(::Type{Float64}, n::BigInt) = Float64(n,RoundNearest)
convert(::Type{Float32}, n::BigInt) = Float32(n,RoundNearest)
convert(::Type{Float16}, n::BigInt) = Float16(n,RoundNearest)

promote_rule{T<:Integer}(::Type{BigInt}, ::Type{T}) = BigInt
if true
# Binary ops
for (fJ, fC) in ((:+, :add), (:-,:sub), (:*, :mul),
                 (:fld, :fdiv_q), (:div, :tdiv_q), (:mod, :fdiv_r), (:rem, :tdiv_r),
                 (:gcd, :gcd), (:lcm, :lcm),
                 (:&, :and), (:|, :ior), (:$, :xor))
    @eval begin
        function ($fJ)(x::BigInt, y::BigInt)
            # r1, a1 = _swap(_ZZ, x)
            # r2, a2 = _swap(_ZZZ, y)
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void,
                  (Ptr{_MPZ}, Ptr{_MPZ}, Ptr{_MPZ}),
                  &_Z, &wrapz(_Z0, x), &wrapz(_Z1, y))
            # _restore(_ZZ, r1, a1)
            # _restore(_ZZZ, r2, a2)
            return BigInt(_Z)
        end
    end
end
else

# Binary ops
for (fJ, fC) in ((:+, :add), (:-,:sub), (:*, :mul),
                 (:fld, :fdiv_q), (:div, :tdiv_q), (:mod, :fdiv_r), (:rem, :tdiv_r),
                 (:gcd, :gcd), (:lcm, :lcm),
                 (:&, :and), (:|, :ior), (:$, :xor))
    @eval begin
        function ($fJ)(x::BigInt, y::BigInt)
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void,
                  (Ptr{_MPZ}, Ptr{MPZ}, Ptr{MPZ}),
                  &_Z, &MPZ(x), &MPZ(y))
            return BigInt(_Z)
        end
    end
end

end
function invmod(x::BigInt, y::BigInt)
    y = abs(y)
    if y == 1
        return big(0)
    end
    if (y==0 || ccall((:__gmpz_invert, :libgmp), Cint,
                      (Ptr{_MPZ}, Ptr{MPZ}, Ptr{MPZ}), &_Z, &MPZ(x), &MPZ(y)) == 0)
        error("no inverse exists")
    end
    return BigInt(_Z)
end

# More efficient commutative operations
for (fJ, fC) in ((:+, :add), (:*, :mul), (:&, :and), (:|, :ior), (:$, :xor))
    @eval begin
        function ($fJ)(a::BigInt, b::BigInt, c::BigInt)
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}, Ptr{MPZ}), &_Z, &MPZ(a), &MPZ(b))
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void, (Ptr{_MPZ}, Ptr{_MPZ}, Ptr{MPZ}), &_Z, &_Z, &MPZ(c))
            return BigInt(_Z)
        end
        function ($fJ)(a::BigInt, b::BigInt, c::BigInt, d::BigInt)
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}, Ptr{MPZ}), &_Z, &MPZ(a), &MPZ(b))
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void, (Ptr{_MPZ}, Ptr{_MPZ}, Ptr{MPZ}), &_Z, &_Z, &MPZ(c))
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void, (Ptr{_MPZ}, Ptr{_MPZ}, Ptr{MPZ}), &_Z, &_Z, &MPZ(d))
            return BigInt(_Z)
        end
        function ($fJ)(a::BigInt, b::BigInt, c::BigInt, d::BigInt, e::BigInt)
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}, Ptr{MPZ}), &_Z, &MPZ(a), &MPZ(b))
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void, (Ptr{_MPZ}, Ptr{_MPZ}, Ptr{MPZ}), &_Z, &_Z, &MPZ(c))
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void, (Ptr{_MPZ}, Ptr{_MPZ}, Ptr{MPZ}), &_Z, &_Z, &MPZ(d))
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void, (Ptr{_MPZ}, Ptr{_MPZ}, Ptr{MPZ}), &_Z, &_Z, &MPZ(e))
            return BigInt(_Z)
        end
    end
end


# Basic arithmetic without promotion
function +(x::BigInt, c::CulongMax)
    ccall((:__gmpz_add_ui, :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ1}, Culong),
          # &_Z, &wrapz(_Z0, x), c)
          &_Z, &MPZ1(x), c)
    return BigInt(_Z)
end
+(c::CulongMax, x::BigInt) = x + c

function -(x::BigInt, c::CulongMax)
    ccall((:__gmpz_sub_ui, :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}, Culong),
          &_Z, &MPZ(x), c)
    return BigInt(_Z)
end
function -(c::CulongMax, x::BigInt)
    ccall((:__gmpz_ui_sub, :libgmp), Void, (Ptr{_MPZ}, Culong, Ptr{MPZ}),
          &_Z, c, &MPZ(x))
    return BigInt(_Z)
end
+(x::BigInt, c::ClongMax) = c < 0 ? -(x, -(c % Culong)) : x + convert(Culong, c)
+(c::ClongMax, x::BigInt) = c < 0 ? -(x, -(c % Culong)) : x + convert(Culong, c)
-(x::BigInt, c::ClongMax) = c < 0 ? +(x, -(c % Culong)) : -(x, convert(Culong, c))
-(c::ClongMax, x::BigInt) = c < 0 ? -(x + -(c % Culong)) : -(convert(Culong, c), x)

function *(x::BigInt, c::CulongMax)
    ccall((:__gmpz_mul_ui, :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}, Culong),
          &_Z, &MPZ(x), c)
    return BigInt(_Z)
end
*(c::CulongMax, x::BigInt) = x * c
function *(x::BigInt, c::ClongMax)
    ccall((:__gmpz_mul_si, :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}, Clong),
          &_Z, &MPZ(x), c)
    return BigInt(_Z)
end
*(c::ClongMax, x::BigInt) = x * c

# unary ops
for (fJ, fC) in ((:-, :neg), (:~, :com))
    @eval begin
        function ($fJ)(x::BigInt)
            ccall(($(string(:__gmpz_,fC)), :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}),
                  &_Z, &MPZ(x))
            return BigInt(_Z)
        end
    end
end

function <<(x::BigInt, c::Int)
    c < 0 && throw(DomainError())
    c == 0 && return x
    ccall((:__gmpz_mul_2exp, :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}, Culong),
          &_Z, &MPZ(x), c)
    return BigInt(_Z)
end

function >>(x::BigInt, c::Int)
    c < 0 && throw(DomainError())
    c == 0 && return x
    ccall((:__gmpz_fdiv_q_2exp, :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}, Culong),
          &_Z, &MPZ(x), c)
    return BigInt(_Z)
end

>>>(x::BigInt, c::Int) = x >> c

trailing_zeros(x::BigInt) = Int(ccall((:__gmpz_scan1, :libgmp), Culong,
                                      (Ptr{MPZ}, Culong), &MPZ(x), 0))
trailing_ones(x::BigInt) = Int(ccall((:__gmpz_scan0, :libgmp), Culong,
                                     (Ptr{MPZ}, Culong), &MPZ(x), 0))

count_ones(x::BigInt) = Int(ccall((:__gmpz_popcount, :libgmp), Culong,
                                  (Ptr{MPZ},), &MPZ(x)))

function divrem(x::BigInt, y::BigInt)
    ccall((:__gmpz_tdiv_qr, :libgmp), Void, (Ptr{_MPZ}, Ptr{_MPZ}, Ptr{MPZ}, Ptr{MPZ}), &_Z, &_ZZ, &MPZ(x), &MPZ(y))
    BigInt(_Z), BigInt(_ZZ)
end

function cmp(x::BigInt, y::BigInt)
    ccall((:__gmpz_cmp, :libgmp), Int32, (Ptr{MPZ}, Ptr{MPZ}), &MPZ(x), &MPZ(y))
end
function cmp(x::BigInt, y::ClongMax)
    ccall((:__gmpz_cmp_si, :libgmp), Int32, (Ptr{MPZ}, Clong), &MPZ(x), y)
end
function cmp(x::BigInt, y::CulongMax)
    ccall((:__gmpz_cmp_ui, :libgmp), Int32, (Ptr{MPZ}, Culong), &MPZ(x), y)
end
cmp(x::BigInt, y::Integer) = cmp(x,big(y))
cmp(x::Integer, y::BigInt) = -cmp(y,x)

function cmp(x::BigInt, y::CdoubleMax)
    isnan(y) && throw(DomainError())
    ccall((:__gmpz_cmp_d, :libgmp), Int32, (Ptr{MPZ}, Cdouble), &MPZ(x), y)
end
cmp(x::CdoubleMax, y::BigInt) = -cmp(y,x)

function isqrt(x::BigInt)
    ccall((:__gmpz_sqrt, :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}), &_Z, &MPZ(x))
    return BigInt(_Z)
end

function ^(x::BigInt, y::Culong)
    ccall((:__gmpz_pow_ui, :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}, Culong),
          &_Z, &MPZ(x), y)
    return BigInt(_Z)
end

function bigint_pow(x::BigInt, y::Integer)
    if y<0; throw(DomainError()); end
    if x== 1; return x; end
    if x==-1; return isodd(y) ? x : -x; end
    if y>typemax(Culong)
       x==0 && return x

       #At this point, x is not 1, 0 or -1 and it is not possible to use
       #gmpz_pow_ui to compute the answer. Note that the magnitude of the
       #answer is:
       #- at least 2^(2^32-1) ≈ 10^(1.3e9) (if Culong === UInt32).
       #- at least 2^(2^64-1) ≈ 10^(5.5e18) (if Culong === UInt64).
       #
       #Assume that the answer will definitely overflow.

       throw(OverflowError())
    end
    return x^convert(Culong, y)
end

^(x::BigInt , y::BigInt ) = bigint_pow(x, y)
^(x::BigInt , y::Bool   ) = y ? x : one(x)
^(x::BigInt , y::Integer) = bigint_pow(x, y)
^(x::Integer, y::BigInt ) = bigint_pow(BigInt(x), y)

function powermod(x::BigInt, p::BigInt, m::BigInt)
    p < 0 && throw(DomainError())
    ccall((:__gmpz_powm, :libgmp), Void,
          (Ptr{_MPZ}, Ptr{MPZ}, Ptr{MPZ}, Ptr{MPZ}),
          &_Z, &MPZ(x), &MPZ(p), &MPZ(m))
    r = BigInt(_Z)
    return m < 0 && r > 0 ? r + m : r # choose sign conistent with mod(x^p, m)
end
powermod(x::BigInt, p::Integer, m::BigInt) = powermod(x, BigInt(p), m)
powermod(x::BigInt, p::Integer, m::Integer) = powermod(x, BigInt(p), BigInt(m))

function gcdx(a::BigInt, b::BigInt)
    if b == 0 # shortcut this to ensure consistent results with gcdx(a,b)
        return a < 0 ? (-a,-one(BigInt),zero(BigInt)) : (a,one(BigInt),zero(BigInt))
    end
    ccall((:__gmpz_gcdext, :libgmp), Void,
          (Ptr{_MPZ}, Ptr{_MPZ}, Ptr{_MPZ}, Ptr{MPZ}, Ptr{MPZ}),
          &_Z, &_ZZ, &_ZZ, &MPZ(a), &MPZ(b))
    g, s, t = BigInt(_Z), BigInt(_ZZ), BigInt(_ZZZ)
    if t == 0
        # work around a difference in some versions of GMP
        if a == b
            return g, t, s
        elseif abs(a)==abs(b)
            return g, t, -s
        end
    end
    g, s, t
end

function sum(arr::AbstractArray{BigInt})
    _Z.size = 0 # TODO: check this is OK
    for i in arr
        ccall((:__gmpz_add, :libgmp), Void,
            (Ptr{_MPZ}, Ptr{_MPZ}, Ptr{MPZ}),
            &_Z, &_Z, &MPZ(i))
    end
    return BigInt(_Z)
end

function factorial(x::BigInt)
    x.size < 0 && return BigInt(0)
    ccall((:__gmpz_fac_ui, :libgmp), Void, (Ptr{_MPZ}, Culong), &_Z, x)
    return BigInt(_Z)
end

function binomial(n::BigInt, k::UInt)
    ccall((:__gmpz_bin_ui, :libgmp), Void, (Ptr{_MPZ}, Ptr{MPZ}, Culong),
          &_Z, &MPZ(n), k)
    return BigInt(_Z)
end
binomial(n::BigInt, k::Integer) = k < 0 ? BigInt(0) : binomial(n, UInt(k))

==(x::BigInt, y::BigInt) = cmp(x,y) == 0
==(x::BigInt, i::Integer) = cmp(x,i) == 0
==(i::Integer, x::BigInt) = cmp(x,i) == 0
==(x::BigInt, f::CdoubleMax) = isnan(f) ? false : cmp(x,f) == 0
==(f::CdoubleMax, x::BigInt) = isnan(f) ? false : cmp(x,f) == 0

<=(x::BigInt, y::BigInt) = cmp(x,y) <= 0
<=(x::BigInt, i::Integer) = cmp(x,i) <= 0
<=(i::Integer, x::BigInt) = cmp(x,i) >= 0
<=(x::BigInt, f::CdoubleMax) = isnan(f) ? false : cmp(x,f) <= 0
<=(f::CdoubleMax, x::BigInt) = isnan(f) ? false : cmp(x,f) >= 0

<(x::BigInt, y::BigInt) = cmp(x,y) < 0
<(x::BigInt, i::Integer) = cmp(x,i) < 0
<(i::Integer, x::BigInt) = cmp(x,i) > 0
<(x::BigInt, f::CdoubleMax) = isnan(f) ? false : cmp(x,f) < 0
<(f::CdoubleMax, x::BigInt) = isnan(f) ? false : cmp(x,f) > 0

string(x::BigInt) = dec(x)
show(io::IO, x::BigInt) = print(io, string(x))

bin(n::BigInt) = base( 2, n)
oct(n::BigInt) = base( 8, n)
dec(n::BigInt) = base(10, n)
hex(n::BigInt) = base(16, n)

function base(b::Integer, n::BigInt)
    2 <= b <= 62 || throw(ArgumentError("base must be 2 ≤ base ≤ 62, got $b"))
    p = ccall((:__gmpz_get_str,:libgmp), Ptr{UInt8}, (Ptr{UInt8}, Cint, Ptr{MPZ}),
              C_NULL, b, &MPZ(n))
    len = Int(ccall(:strlen, Csize_t, (Ptr{UInt8},), p))
    ASCIIString(pointer_to_array(p,len,true))
end

function ndigits0z(x::BigInt, b::Integer=10)
    b < 2 && throw(DomainError())
    if ispow2(b)
        Int(ccall((:__gmpz_sizeinbase,:libgmp), Culong, (Ptr{MPZ}, Int32), &MPZ(x), b))
    else
        # non-base 2 mpz_sizeinbase might return an answer 1 too big
        # use property that log(b, x) < ndigits(x, b) <= log(b, x) + 1
        n = Int(ccall((:__gmpz_sizeinbase,:libgmp), Culong, (Ptr{MPZ}, Int32), &MPZ(x), 2))
        lb = log2(b) # assumed accurate to <1ulp (true for openlibm)
        q,r = divrem(n,lb)
        iq = Int(q)
        maxerr = q*eps(lb) # maximum error in remainder
        if r-1.0 < maxerr
            abs(x) >= big(b)^iq ? iq+1 : iq
        elseif lb-r < maxerr
            abs(x) >= big(b)^(iq+1) ? iq+2 : iq+1
        else
            iq+1
        end
    end
end
ndigits(x::BigInt, b::Integer=10) = x.size == 0 ? 1 : ndigits0z(x,b)

isprime(x::BigInt, reps=25) = ccall((:__gmpz_probab_prime_p,:libgmp), Cint, (Ptr{MPZ}, Cint), &MPZ(x), reps) > 0

prevpow2(x::BigInt) = x.size < 0 ? -prevpow2(-x) : (x <= 2 ? x : one(BigInt) << (ndigits(x, 2)-1))
nextpow2(x::BigInt) = x.size < 0 ? -nextpow2(-x) : (x <= 2 ? x : one(BigInt) << ndigits(x-1, 2))

Base.checked_add(a::BigInt, b::BigInt) = a + b
Base.checked_sub(a::BigInt, b::BigInt) = a - b
Base.checked_mul(a::BigInt, b::BigInt) = a * b

end # module
