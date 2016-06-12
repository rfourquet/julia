# This file is a part of Julia. License is MIT: http://julialang.org/license

module dSFMT

export DSFMT_state, dsfmt_get_min_array_size, dsfmt_get_idstring,
       dsfmt_init_gen_rand, dsfmt_init_by_array, dsfmt_gv_init_by_array,
       dsfmt_fill_array_close_open!, dsfmt_fill_array_close1_open2!,
       win32_SystemFunction036!

"Mersenne Exponent"
const MEXP = 19937
"DSFMT internal state array size of N 128-bit integers."
const N    = floor(Int, ((MEXP - 128) / 104 + 1))
"""Julia DSFMT state representation size counted in 32-bit integers.

Size: (DSFMT state array of Int128 + 1)*4 + Int32 index + Int32 padding
"""
const JN32 = (N+1)*4+1+1

"Characteristic polynomial used by dSFMT with exponent 19937"
const Poly19937String = "10455110544511444054554514541dbbb0a20820a288a00a80a82208280b73237d2ff2ab5e2fcac914510101df18802aaaa08a022820a02aaa202ae822c364b91fb08598fe4410154041f028a266586e59cf12ce316b3a56af45cb49d02c7059cb89d2d81b0d288badbb25fa4e53b280aa88a22aa82abe7fc0645b7d7a4650c1dec48f21224e3d0e6e04c062c2273ef0d8361415c724dbc8f79118d5fac429f35dc460f6007e54c3966c28808e4c9308cc46e2e0e153bd922223796d4101af867e16e6641e6831e06ebbd2beaf52b2b47076dbf3a3e36c6d14d19dbf5d4b2b44b4d3aa6e1ea102578d765f08e1cb0749220075b8aae81c6e99692a56b35ddd4cf91b1034f1398c98e2d4ac8dbed09bc73ede098514cf3ffdf45cbb59335e3ec42f5f6a5672acc4ca8daa02a2502350ac0485f8b36f27d7a1d4d4b22fc7601e22a4f7c6ba53782b335837a21a068e8fcf3fdebb28860157301519cdea328b1ef4b8d5bc512ce65ff33298c34cc98ea1558f7b6d4db594f4bcab58d9f7bcf5cc59e259216de13f77569bbcee1c8abd55de985b7129e611d156c08cafa022ad7a2206a34a61e5c4c91e75495112003ec03c182a0155d9221382d0b30f45a00d6c19740f9ecebb448de78dfc0342f14166f54afdb97d00ac1a390355ce2aa9de1b3c919d8dd188fc9451ce9c86fa560a2da9dcaa681efd21fe5b6055f8e35a833e5704936245d06e387bf9956251bf0a252628be7a3cb0edab4aaaf141e6d7a9929cc03afa76ca433016d880def9e4cf10f7274e58aa35c372b7b7fb210fe0dc1a6b8445e7774ad6001b9aa1f2a01a790ee849e7ac810e0a646e733a7121bd727a9b593e0c9f5306dff5105af5967e3cee81069100d7e91a9c266e64c9e073a6e527765308879b22ca062668f9a564da6314dcad51405f160e8259582b7c06c313c84b0acba44958c052e6be540a7688e240232bee40b990dc48ee07d560786ca34e7df1bbdd2bca38a30c548ec57e91906b8417ff0da68db9c154d8ad83b06a6fc2b2e14ca5fbe7bd50382949c9b1f6e8540d9d43b35fa76a6ded27c2f17095a4f330626c5e86e8ff88ae53e05a434356a04a1ddae43b6e2ab883719360fbece72b6090ab17414ca7006e49d183813422c808fde53a30f872254bb554653aef86855f95a9361782100de2402efd749cc8cf6a837066c1c40c0160e415d8119e53a09877f1160ef8b99b2839e9b8c09b1e461e906041344c8fc2ef0a8eda04e319da41e001e60bc64dcdfc0593dff0f4b390580e1cd5b3c16204e77df10217791f99de49fcdc9160b793fd980bff7ae0cbd570425eb439352e5032e03797461376b5fb92aa156ad64935cc201a162f10f04b6d2d20a0415ae16f299e98baa86466f6f517f05f430254884a4010ac196540b0644e3c274323d4f0206780d38175f1e41fcb65bd387be073abee61b99d43f6b9106953ae4f6906e6ac0741e26af05fa9150c4f380558668aa667e404e3784b839d631e35af015024dbfc3dce4685574cd1e58eb72c70011090a2a876b65e34cb6cf297d24cb61ccca5a9706f34ae1f66345998f850de4e48d77cdf6e00fb0d2210ec9fb53fed02a781f7dfcdb609b9f955504f450e4b7b623cb0f5ba1ea09d92cd8d14f7e827b4580855f3a7dc2e5a45817df9e26adb5934f6026f745cb0f65e71c590bd954d1abc3826379719b7c6f4a0cbe6eb22a903b98bef785bb96efe2fc96988722c91f3e59d28d8244c8bfb59ee26082d82cad937ee70f178b44082533308ca24f236d8b91ca7af5b3d865c90d61410e1ffe39be6433a12ef2932e101b4bb34befa76748e0364a96f06e7932f44297fd5f85765b662c3ade19d9a9d9479f6de20b6b753d3dcbadf63e344578b98af85b4c4c63be9d154864f5d341f210f3503a60efec38ee59069499d0049aedfaef9264a7ce9de460a01e5437254fc68dfaebaa5e0e791380806bc149aedbc1d771457770937a5d606fc5ae728993783e6c45e1f5e1b9492a32f9df46a01020792a3803af04837a3905e7cc6ae68c512cb58f4facb457476729bac1ac89a7a32dc6857edbd6624ebeffed9d4e84a2f4ded9759962635aac94ca72d039c14af6e932fc84c25de28688acab0f41ae931a0f35b9c4195483d902f95e0d3e745e08f334cf5062da9fbd18fbb9efeb275a50a8a479939aa3e376821a030f0d241a4c4f6e3298a43a7f2166db483946c5ca623087b6252e27b09805d92a834ad914b9555f9c36150bb17d7e85f6b1a10b41a5c36a1fd0fdc354ec91720b245b0abcde6b38fdd33f471aa6ba1dbb4f178c3c6d8140a1f0700e072b0f9aafe1208abc94eea750b84e74ba6781b48c398ddfd2842e5447a11767e4f467864e4447382379010669f07870339ca42ac290063b40eaba1daa63cf6cd70c5a600c018f6933dc8bec000a521344cad7320ba121dd21f4723d38a8d3ab8c1f0f6c5a6995b796af79407ae1a7ce6d78922677d9990dd2a588f8a3323d80e9a69417f5224565afa60b64604e7316229514dcb7282b4e638981a5751d114da1ac9bf31f0e2fff5213f2020f9f2f31a8fd0c614e80c1a056d4b1af3ded2f696578f56427962ca54f4a28a502a0ac59013416abd81515fb1956ccb494c05ef61cab48474b6b1609cc5a3871a5111f8bf0a76b378f0e646687829e30f5762156da66c1b1c7abc0eb84e6ff2b9f5b22d34540ab97d643e8dd2e35f6e9e4fc2c30d8af88b2caab7bd5d4a6cf967e8ef79967c1ae85bf7d410a79f4630f13fdc6507d339909b81a29d84741103371310e5b4e279758431df627553b6826fc4c98e5fb6551315b0bd811b7b0f357198210dd99ccd8fba2904114c3e0b344eba43832b3c507e8b6b586e4ab3dc7a2ec71e150c54a13eca2340328d0b3e419ab2ba862ee93fc239fb46d907628055e105318e7fa52f9a83deb0e3cb02c62b8817702ead02a315f76aa1d08860cc5214a867808e33f8e075241956f148f876f3bc66566773610c9c5935b559c0ac47d84b6bfb112f59842be58df51055cf9180264f53f7795d4c934718bc65f359e34a8d230408854685b59c3a9f4d73a229bb465d4da3165404c6786c767299f57dfa85a83492fb4f61386441c928224cd88a7f4b36f245b7aa2b5c97b545ac4db8afe9a1a87e27b57d94c2bbffdb6e88f812aa27e0908048812086c2a72289d7bf136b3a1042a44d1913d39caec24ffda22814706f080b6cbe00e9cd442ccdcb600a436c0daeacbc5482021ba8a06c1fedbb333793557d5175b9313799ff91dfa620380a9e2a10132f0818bba72072e359726e2bd1f2ec98e0face32e0f88ee2c6f7cef7c2fbceffe8d3ccdff97b7ff71d861ba8b98237ccfb00176ee02206ccc08026cee082a88a8a349a1c9016983ea10789272105032f89b3113fd9b75b35c884622ec884622ee8aee2aaa2aeae86868c868ea68ea6862e0624062ea22aa66ee66ee44ee64ce64ce64ce646464c4808081808080a0a0828282828282822222a8898888888888aaaa2aaaaaaaaaaaaa2000000000000000008"


type DSFMT_state
    val::Vector{Int32}
    DSFMT_state() = new(Array{Int32}(JN32))
    DSFMT_state(val::Vector{Int32}) = new(val)
end

function dsfmt_get_idstring()
    idstring = ccall((:dsfmt_get_idstring,:libdSFMT),
                     Ptr{UInt8},
                     ())
    return unsafe_string(idstring)
end

function dsfmt_get_min_array_size()
    min_array_size = ccall((:dsfmt_get_min_array_size,:libdSFMT),
                           Int32,
                           ())
end

const dsfmt_min_array_size = dsfmt_get_min_array_size()

function dsfmt_init_gen_rand(s::DSFMT_state, seed::UInt32)
    ccall((:dsfmt_init_gen_rand,:libdSFMT),
          Void,
          (Ptr{Void}, UInt32,),
          s.val, seed)
end

function dsfmt_init_by_array(s::DSFMT_state, seed::Vector{UInt32})
    ccall((:dsfmt_init_by_array,:libdSFMT),
          Void,
          (Ptr{Void}, Ptr{UInt32}, Int32),
          s.val, seed, length(seed))
end

function dsfmt_gv_init_by_array(seed::Vector{UInt32})
    ccall((:dsfmt_gv_init_by_array,:libdSFMT),
          Void,
          (Ptr{UInt32}, Int32),
          seed, length(seed))
end

function dsfmt_fill_array_close1_open2!(s::DSFMT_state, A::Ptr{Float64}, n::Int)
    @assert Csize_t(A) % 16 == 0 # the underlying C array must be 16-byte aligned
    @assert dsfmt_min_array_size <= n && iseven(n)
    ccall((:dsfmt_fill_array_close1_open2,:libdSFMT),
          Void,
          (Ptr{Void}, Ptr{Float64}, Int),
          s.val, A, n)
end

function dsfmt_fill_array_close_open!(s::DSFMT_state, A::Ptr{Float64}, n::Int)
    @assert Csize_t(A) % 16 == 0 # the underlying C array must be 16-byte aligned
    @assert dsfmt_min_array_size <= n && iseven(n)
    ccall((:dsfmt_fill_array_close_open,:libdSFMT),
          Void,
          (Ptr{Void}, Ptr{Float64}, Int),
          s.val, A, n)
end

# dSFMT jump poly calculation

"Represents a polynomial in GF(2)[X]"
immutable GF2X
    z::BigInt
end

GF2X(s::AbstractString) = GF2X(parse(BigInt, reverse(s), 16))
Base.string(f::GF2X) = reverse(base(16, f.z))

degree(f::GF2X) = Base.ndigits0z(f.z, 2) - 1

tstbit(z::BigInt, i) = ccall((:__gmpz_tstbit, :libgmp), Cint, (Ptr{BigInt}, Culong), &z, i) % Int
coeff(f::GF2X, i) = tstbit(f.z, i)

div2!(z::BigInt, c::Int=1) = (ccall((:__gmpz_fdiv_q_2exp, :libgmp), Void, (Ptr{BigInt}, Ptr{BigInt}, Culong), &z, &z, c); z)
divx!(f::GF2X, c::Int=1) = (div2!(f.z); f)
mulx!(f::GF2X, c::Int=1) = (ccall((:__gmpz_mul_2exp, :libgmp), Void, (Ptr{BigInt}, Ptr{BigInt}, Culong), &f.z, &f.z, c); f)
xor!(f::GF2X, g::GF2X) = (ccall((:__gmpz_xor, :libgmp), Void, (Ptr{BigInt}, Ptr{BigInt}, Ptr{BigInt}), &f.z, &f.z, &g.z); f)


const _squarres = Dict{GF2X, Vector{GF2X}}()

function mulxmod!(f::GF2X, m::GF2X, deg=degree(m))
    mulx!(f)
    degree(f) == deg && xor!(f, m)
    f
end

const _sqrmod_coeffs = Vector{Int}()

function sqrmod!(f::GF2X, m::GF2X)
    sqrs = get!(()->Vector{GF2X}(), _squarres, m)
    degree(f) < 1 && return f # filter below cannot be empty
    d = degree(m)
    d > 1 || throw(DomainError())
    if isempty(sqrs)
        resize!(sqrs, d)
        x2i = GF2X(1)
        for i=1:d
            mulxmod!(x2i, m, d)
            mulxmod!(x2i, m, d)
            sqrs[i] = GF2X(x2i.z+0)
        end
    end
    # note: not slower that the non-allocating equivalent
    foldl(xor!, GF2X(coeff(f, 0)),
          sqrs[i] for i in filter(j->coeff(f, j)==1, 1:degree(f)))
#=
    empty!(_sqrmod_coeffs)
    for i in 1:degree(f)
        coeff(f, i) == 1 && push!(_sqrmod_coeffs, i)
    end
    ccall((:__gmpz_set_si, :libgmp), Void, (Ptr{BigInt}, Clong), &f.z, coeff(f, 0))
    for i in _sqrmod_coeffs
        @inbounds xor!(f, sqrs[i])
    end
    f
    =#
end

function powxmod(e::BigInt, m::GF2X)
    # X^e mod m
    f = GF2X(1)
    d = degree(m)
    for i = Base.ndigits0z(e, 2)-1:-1:0
        f = sqrmod!(f, m)
        if tstbit(e, i) == 1
            f = mulxmod!(f, m, d)
        end
    end
    f
end

function reducemod!(f::GF2X, m::GF2X)
    n = degree(m)
    while true
        k = degree(f)
        k < n && return f
        xor!(f, GF2X(m << (k-n)))
    end
end

const Poly19937Ref = Ref{GF2X}()

__init__() = Poly19937Ref[] = GF2X(Poly19937String)

calc_jump(step::Integer, charpoly::GF2X=Poly19937Ref[]) = powxmod(big(step), charpoly)

const JumpPolys = Dict{BigInt,GF2X}()

get_jump(step::Integer) = get!(()->calc_jump(step), JumpPolys, step)


# dSFMT jump
function dsfmt_jump(s::DSFMT_state, jp::GF2X)
    index = s.val[end-1]
    work = zeros(UInt64, JN32>>1)
    dsfmt = reinterpret(UInt64, copy(s.val))
    dsfmt[end] = UInt64(N*2)
    for i in 0:degree(jp)
        coeff(jp, i) == 1 && dsfmt_jump_add!(work, dsfmt)
        dsfmt_jump_next_state!(dsfmt)
    end
    work[end] = index
    return DSFMT_state(reinterpret(Int32, work))
end

function dsfmt_jump_add!(dest::Vector{UInt64}, src::Vector{UInt64})
    dp = dest[end] >> 1
    sp = src[end] >> 1
    diff = ((sp - dp + N) % N)
    i = 1
    while i <= N-diff
        j = i*2-1
        p = j + diff*2
        dest[j]   $= src[p]
        dest[j+1] $= src[p+1]
        i += 1
    end
    while i <= N
        j = i*2-1
        p = j + (diff - N)*2
        dest[j]   $= src[p]
        dest[j+1] $= src[p+1]
        i += 1
    end
    dest[N*2+1] $= src[N*2+1]
    dest[N*2+2] $= src[N*2+2]
    return dest
end

function dsfmt_jump_next_state!(mts::Vector{UInt64})
    POS1 = 117
    SL1  = 19
    SR   = 12
    MSK1 = 0x000ffafffffffb3f
    MSK2 = 0x000ffdfffc90fffd

    idx = (mts[end] >> 1) % N

    a = idx*2+1
    b = ((idx + POS1) % N)*2+1
    u = N*2+1

    t0 = mts[a]
    t1 = mts[a+1]
    L0 = mts[u]
    L1 = mts[u+1]
    mts[u]   = (t0 << SL1) $ (L1 >> 32) $ (L1 << 32) $ mts[b]
    mts[u+1] = (t1 << SL1) $ (L0 >> 32) $ (L0 << 32) $ mts[b+1]
    mts[a]   = (mts[u]   >> SR) $ (mts[u]   & MSK1) $ t0
    mts[a+1] = (mts[u+1] >> SR) $ (mts[u+1] & MSK2) $ t1

    mts[end] = (mts[end] + 2) % (N*2)
    return mts
end



## Windows entropy

if is_windows()
    function win32_SystemFunction036!{T}(a::Array{T})
        ccall((:SystemFunction036, :Advapi32), stdcall, UInt8, (Ptr{Void}, UInt32), a, sizeof(a))
    end
end




end # module
