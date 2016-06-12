# This file is a part of Julia. License is MIT: http://julialang.org/license

# Issue #6573
srand(0); rand(); x = rand(384);
@test find(x .== rand()) == []

@test rand() != rand()
@test 0.0 <= rand() < 1.0
@test rand(UInt32) >= 0
@test -10 <= rand(-10:-5) <= -5
@test -10 <= rand(-10:5) <= 5
@test minimum([rand(Int32(1):Int32(7^7)) for i = 1:100000]) > 0
@test(typeof(rand(false:true)) === Bool)
@test(typeof(rand(Char)) === Char)
@test length(randn(4, 5)) == 20
@test length(bitrand(4, 5)) == 20

@test rand(MersenneTwister()) == 0.8236475079774124
@test rand(MersenneTwister(0)) == 0.8236475079774124
@test rand(MersenneTwister(42)) == 0.5331830160438613
# Try a seed larger than 2^32
@test rand(MersenneTwister(5294967296)) == 0.3498809918210497

# Test array filling, Issues #7643, #8360
@test rand(MersenneTwister(0), 1) == [0.8236475079774124]
A = zeros(2, 2)
rand!(MersenneTwister(0), A)
@test A == [0.8236475079774124  0.16456579813368521;
            0.9103565379264364  0.17732884646626457]
A = zeros(2, 2)
@test_throws BoundsError rand!(MersenneTwister(0), A, 5)
@test rand(MersenneTwister(0), Int64, 1) == [4439861565447045202]
A = zeros(Int64, 2, 2)
rand!(MersenneTwister(0), A)
@test A == [858542123778948672  5715075217119798169;
            8690327730555225005 8435109092665372532]
A = zeros(UInt128, 2, 2)
@test_throws BoundsError rand!(MersenneTwister(0), A, 5)

# rand from AbstractArray
let mt = MersenneTwister()
    srand(mt)
    @test rand(mt, 0:3:1000) in 0:3:1000
    @test issubset(rand!(mt, Array{Int}(100), 0:3:1000), 0:3:1000)
    coll = Any[2, UInt128(128), big(619), "string"]
    @test rand(mt, coll) in coll
    @test issubset(rand(mt, coll, 2, 3), coll)

    # check API with default RNG:
    rand(0:3:1000)
    rand!(Array{Int}(100), 0:3:1000)
    rand(coll)
    rand(coll, 2, 3)
end

# randn
@test randn(MersenneTwister(42)) == -0.5560268761463861
A = zeros(2, 2)
randn!(MersenneTwister(42), A)
@test A == [-0.5560268761463861  0.027155338009193845;
            -0.444383357109696  -0.29948409035891055]

for T in (Int8, UInt8, Int16, UInt16, Int32, UInt32, Int64, UInt64, Int128, UInt128, BigInt,
          Float16, Float32, Float64, Rational{Int})
    r = rand(convert(T, 97):convert(T, 122))
    @test typeof(r) == T
    @test 97 <= r <= 122
    r = rand(convert(T, 97):convert(T,2):convert(T, 122),2)[1]
    @test typeof(r) == T
    @test 97 <= r <= 122
    @test mod(r,2)==1

    if T<:Integer && !(T===BigInt)
        x = rand(typemin(T):typemax(T))
        @test isa(x,T)
        @test typemin(T) <= x <= typemax(T)
    end
end

@test !any([(Base.Random.maxmultiple(i)+i) > 0xFF for i in 0x00:0xFF])
@test all([(Base.Random.maxmultiple(i)+1) % i for i in 0x01:0xFF] .== 0)
@test all([(Base.Random.maxmultiple(i)+1+i) > 0xFF for i in 0x00:0xFF])
@test length(0x00:0xFF)== Base.Random.maxmultiple(0x0)+1


if sizeof(Int32) < sizeof(Int)
    r = rand(Int32(-1):typemax(Int32))
    @test typeof(r) == Int32
    @test -1 <= r <= typemax(Int32)
    @test all([div(0x00010000000000000000,k)*k - 1 == Base.Random.RangeGenerator(map(UInt64,1:k)).u for k in 13 .+ Int64(2).^(32:62)])
    @test all([div(0x00010000000000000000,k)*k - 1 == Base.Random.RangeGenerator(map(Int64,1:k)).u for k in 13 .+ Int64(2).^(32:61)])

    @test Base.Random.maxmultiplemix(0x000100000000) === 0xffffffffffffffff
    @test Base.Random.maxmultiplemix(0x0000FFFFFFFF) === 0x00000000fffffffe
    @test Base.Random.maxmultiplemix(0x000000000000) === 0xffffffffffffffff
end

# BigInt specific
for T in [UInt32, UInt64, UInt128, Int128]
    s = big(typemax(T)-1000) : big(typemax(T)) + 10000
    @test rand(s) != rand(s)
    @test big(typemax(T)-1000) <= rand(s) <= big(typemax(T)) + 10000
    r = rand(s, 1, 2)
    @test size(r) == (1, 2)
    @test typeof(r) == Matrix{BigInt}

    srand(0)
    r = rand(s)
    srand(0)
    @test rand(s) == r
end

# Test ziggurat tables
ziggurat_table_size = 256
nmantissa           = Int64(2)^51 # one bit for the sign
ziggurat_nor_r      = parse(BigFloat,"3.65415288536100879635194725185604664812733315920964488827246397029393565706474")
nor_section_area    = ziggurat_nor_r*exp(-ziggurat_nor_r^2/2) + erfc(ziggurat_nor_r/sqrt(BigFloat(2)))*sqrt(big(π)/2)
emantissa           = Int64(2)^52
ziggurat_exp_r      = parse(BigFloat,"7.69711747013104971404462804811408952334296818528283253278834867283241051210533")
exp_section_area    = (ziggurat_exp_r + 1)*exp(-ziggurat_exp_r)

ki = Array{UInt64}(ziggurat_table_size)
wi = Array{Float64}(ziggurat_table_size)
fi = Array{Float64}(ziggurat_table_size)
# Tables for exponential variates
ke = Array{UInt64}(ziggurat_table_size)
we = Array{Float64}(ziggurat_table_size)
fe = Array{Float64}(ziggurat_table_size)
function randmtzig_fill_ziggurat_tables() # Operates on the global arrays
    wib = big(wi)
    fib = big(fi)
    web = big(we)
    feb = big(fe)
    # Ziggurat tables for the normal distribution
    x1 = ziggurat_nor_r
    wib[256] = x1/nmantissa
    fib[256] = exp(-0.5*x1*x1)
    # Index zero is special for tail strip, where Marsaglia and Tsang
    # defines this as
    # k_0 = 2^31 * r * f(r) / v, w_0 = 0.5^31 * v / f(r), f_0 = 1,
    # where v is the area of each strip of the ziggurat.
    ki[1] = trunc(UInt64,x1*fib[256]/nor_section_area*nmantissa)
    wib[1] = nor_section_area/fib[256]/nmantissa
    fib[1] = one(BigFloat)

    for i = 255:-1:2
        # New x is given by x = f^{-1}(v/x_{i+1} + f(x_{i+1})), thus
        # need inverse operator of y = exp(-0.5*x*x) -> x = sqrt(-2*ln(y))
        x = sqrt(-2.0*log(nor_section_area/x1 + fib[i+1]))
        ki[i+1] = trunc(UInt64,x/x1*nmantissa)
        wib[i] = x/nmantissa
        fib[i] = exp(-0.5*x*x)
        x1 = x
    end

    ki[2] = UInt64(0)

    # Zigurrat tables for the exponential distribution
    x1 = ziggurat_exp_r
    web[256] = x1/emantissa
    feb[256] = exp(-x1)

    # Index zero is special for tail strip, where Marsaglia and Tsang
    # defines this as
    # k_0 = 2^32 * r * f(r) / v, w_0 = 0.5^32 * v / f(r), f_0 = 1,
    # where v is the area of each strip of the ziggurat.
    ke[1] = trunc(UInt64,x1*feb[256]/exp_section_area*emantissa)
    web[1] = exp_section_area/feb[256]/emantissa
    feb[1] = one(BigFloat)

    for i = 255:-1:2
        # New x is given by x = f^{-1}(v/x_{i+1} + f(x_{i+1})), thus
        # need inverse operator of y = exp(-x) -> x = -ln(y)
        x = -log(exp_section_area/x1 + feb[i+1])
        ke[i+1] = trunc(UInt64,x/x1*emantissa)
        web[i] = x/emantissa
        feb[i] = exp(-x)
        x1 = x
    end
    ke[2] = zero(UInt64)

    wi[:] = wib
    fi[:] = fib
    we[:] = web
    fe[:] = feb
    return nothing
end
randmtzig_fill_ziggurat_tables()
@test all(ki == Base.Random.ki)
@test all(wi == Base.Random.wi)
@test all(fi == Base.Random.fi)
@test all(ke == Base.Random.ke)
@test all(we == Base.Random.we)
@test all(fe == Base.Random.fe)

#same random numbers on for small ranges on all systems

seed = rand(UInt) #leave state nondeterministic as above
srand(seed)
r = map(Int64,rand(map(Int32,97:122)))
srand(seed)
@test r == rand(map(Int64,97:122))

srand(seed)
r = map(UInt64,rand(map(UInt32,97:122)))
srand(seed)
@test r == rand(map(UInt64,97:122))

@test all([div(0x000100000000,k)*k - 1 == Base.Random.RangeGenerator(map(UInt64,1:k)).u for k in 13 .+ Int64(2).^(1:30)])
@test all([div(0x000100000000,k)*k - 1 == Base.Random.RangeGenerator(map(Int64,1:k)).u for k in 13 .+ Int64(2).^(1:30)])

import Base.Random: uuid1, uuid4, UUID, uuid_version

# UUID
u1 = uuid1()
u4 = uuid4()
@test uuid_version(u1) == 1
@test uuid_version(u4) == 4
@test u1 == UUID(string(u1)) == UUID(utf16(string(u1))) == UUID(utf32(string(u1)))
@test u4 == UUID(string(u4)) == UUID(utf16(string(u4))) == UUID(utf32(string(u4)))
@test u1 == UUID(UInt128(u1))
@test u4 == UUID(UInt128(u4))
@test uuid4(MersenneTwister()) == uuid4(MersenneTwister())
@test_throws ArgumentError UUID("550e8400e29b-41d4-a716-446655440000")
@test_throws ArgumentError UUID("550e8400e29b-41d4-a716-44665544000098")
@test_throws ArgumentError UUID("z50e8400-e29b-41d4-a716-446655440000")

#issue 8257
i8257 = 1:1/3:100
for i = 1:100
    @test rand(i8257) in i8257
end

# test code paths of rand!

let mt = MersenneTwister(0)
    A128 = Array{UInt128}(0)
    @test length(rand!(mt, A128)) == 0
    for (i,n) in enumerate([1, 3, 5, 6, 10, 11, 30])
        resize!(A128, n)
        rand!(mt, A128)
        @test length(A128) == n
        @test A128[end] == UInt128[0x15de6b23025813ad129841f537a04e40,
                                   0xcfa4db38a2c65bc4f18c07dc91125edf,
                                   0x33bec08136f19b54290982449b3900d5,
                                   0xde41af3463e74cb830dad4add353ca20,
                                   0x066d8695ebf85f833427c93416193e1f,
                                   0x48fab49cc9fcee1c920d6dae629af446,
                                   0x4b54632b4619f4eca22675166784d229][i]
    end

    srand(mt,0)
    for (i,T) in enumerate([Int8, UInt8, Int16, UInt16, Int32, UInt32, Int64, UInt64, Int128, Float16, Float32])
        A = Array{T}(16)
        B = Array{T}(31)
        rand!(mt, A)
        rand!(mt, B)
        @test A[end] == Any[21,0x7b,17385,0x3086,-1574090021,0xadcb4460,6797283068698303107,0x4e91c9c4d4f5f759,
                            -3482609696641744459568613291754091152,Float16(0.03125),0.68733835f0][i]

        @test B[end] == Any[49,0x65,-3725,0x719d,814246081,0xdf61843a,-3010919637398300844,0x61b367cf8810985d,
                            -33032345278809823492812856023466859769,Float16(0.95),0.51829386f0][i]
    end

    srand(mt,0)
    AF64 = Array{Float64}(Base.Random.dsfmt_get_min_array_size()-1)
    @test rand!(mt, AF64)[end] == 0.957735065345398
    @test rand!(mt, AF64)[end] == 0.6492481059865669
    resize!(AF64, 2*length(mt.vals))
    @test Base.Random.rand_AbstractArray_Float64!(mt, AF64)[end]  == 0.432757268470779
end

# Issue #9037
let mt = MersenneTwister()
    a = Array{Float64}(0)
    resize!(a, 1000) # could be 8-byte aligned
    b = Array{Float64}(1000) # should be 16-byte aligned
    c8 = Array{UInt64}(1001)
    pc8 = pointer(c8)
    if Int(pc8) % 16 == 0
        # Make sure pc8 is not 16-byte aligned since that's what we want to test.
        # It still has to be 8-byte aligned since it is otherwise invalid on
        # certain architectures (e.g. ARM)
        pc8 += 8
    end
    c = unsafe_wrap(Array, Ptr{Float64}(pc8), 1000) # Int(pointer(c)) % 16 == 8

    for A in (a, b, c)
        srand(mt, 0)
        rand(mt) # this is to fill mt.vals, cf. #9040
        rand!(mt, A) # must not segfault even if Int(pointer(A)) % 16 != 0
        @test A[end-4:end] == [0.49508297796349776,0.3408340446375888,0.3211229457075784,0.9103565379264364,0.16456579813368521]
    end
end

# make sure reading 128-bit ints from RandomDevice works
let a = [rand(RandomDevice(), UInt128) for i=1:10]
    @test reduce(|, a)>>>64 != 0
end

# test all rand APIs
for rng in ([], [MersenneTwister()], [RandomDevice()])
    for f in [rand, randn, randexp]
        f(rng...)        ::Float64
        f(rng..., 5)     ::Vector{Float64}
        f(rng..., 2, 3)  ::Array{Float64, 2}
    end
    for f! in [randn!, randexp!]
        f!(rng..., Array{Float64}(5))    ::Vector{Float64}
        f!(rng..., Array{Float64}(2, 3)) ::Array{Float64, 2}
    end

    bitrand(rng..., 5)             ::BitArray{1}
    bitrand(rng..., 2, 3)          ::BitArray{2}
    rand!(rng..., BitArray(5))     ::BitArray{1}
    rand!(rng..., BitArray(2, 3))  ::BitArray{2}

    for T in [Base.BitInteger_types..., Bool, Float16, Float32, Float64]
        a0 = rand(rng..., T)       ::T
        a1 = rand(rng..., T, 5)    ::Vector{T}
        a2 = rand(rng..., T, 2, 3) ::Array{T, 2}
        if T <: AbstractFloat
            for a in [a0, a1..., a2...]
                @test 0.0 <= a < 1.0
            end
        end
        for A in (Array{T}(5), Array{T}(2, 3))
            X = T == Bool ? T[0,1] : T[0,1,2]
            rand!(rng..., A)            ::typeof(A)
            rand!(rng..., A, X)  ::typeof(A)
            rand!(rng..., sparse(A))            ::typeof(sparse(A))
            rand!(rng..., sparse(A), X)  ::typeof(sparse(A))
        end
    end
end

function hist(X,n)
    v = zeros(Int,n)
    for x in X
        v[floor(Int,x*n)+1] += 1
    end
    v
end

# test uniform distribution of floats
for rng in [srand(MersenneTwister()), RandomDevice()]
    for T in [Float16,Float32,Float64]
        # array version
        counts = hist(rand(rng, T, 2000), 4)
        @test minimum(counts) > 300 # should fail with proba < 1e-26
        # scalar version
        counts = hist([rand(rng, T) for i in 1:2000], 4)
        @test minimum(counts) > 300
    end
end

# test reproducility of methods
let mta = MersenneTwister(42), mtb = MersenneTwister(42)

    @test rand(mta) == rand(mtb)
    @test rand(mta,10) == rand(mtb,10)
    @test randn(mta) == randn(mtb)
    @test randn(mta,10) == randn(mtb,10)
    @test randexp(mta) == randexp(mtb)
    @test randexp(mta,10) == randexp(mtb,10)
    @test rand(mta,1:100) == rand(mtb,1:100)
    @test rand(mta,1:10,10) == rand(mtb,1:10,10)
    @test rand(mta,Bool) == rand(mtb,Bool)
    @test bitrand(mta,10) == bitrand(mtb,10)

    @test randstring(mta) == randstring(mtb)
    @test randstring(mta,10) == randstring(mtb,10)

    @test randsubseq(mta,1:10,0.4) == randsubseq(mtb,1:10,0.4)
    @test randsubseq!(mta,Int[],1:10,0.4) == randsubseq!(mtb,Int[],1:10,0.4)

    @test shuffle(mta,collect(1:10)) == shuffle(mtb,collect(1:10))
    @test shuffle!(mta,collect(1:10)) == shuffle!(mtb,collect(1:10))
    @test shuffle(mta,collect(2:11)) == shuffle(mtb,2:11)

    @test randperm(mta,10) == randperm(mtb,10)
    @test sort!(randperm(10)) == sort!(shuffle(1:10)) == collect(1:10)
    @test randperm(mta,big(10)) == randperm(mtb,big(10)) # cf. #16376
    @test randperm(0) == []
    @test_throws ErrorException randperm(-1)

    @test randcycle(mta,10) == randcycle(mtb,10)

    @test sprand(mta,1,1,0.9) == sprand(mtb,1,1,0.9)
    @test sprand(mta,10,10,0.3) == sprand(mtb,10,10,0.3)
end


# test MersenneTwister polynomial generation
let jump25000 = "35931a4947eeab70a9abbfaca4a79cfcf2610a35a586c6f4e4bdfa826d538cbfb0432c37321fcec4f6c98de3df06685087032988b0ad9a2144562aa82e06f2f6f256b5b412c524e35383a894da7b04e142c4156290585186d8fc06d3141a778220c2519a851b5a9e5947a3f745b71804631988825e21dba40392ff4c036b30d2d013b45e2be94b5e130a9c6424d2e82f48c855c81bd10757fdb5a91e23e9e312e430514ea31631d8897b4cf26eb39b37be0c92706e5637d4b34c1e4046b741e455df195cb512e8e0f8d578175a3da5e00d7ce247d9b92042b1b515d01f7f89fe661ebccb06dfb77bc0fbb99806921b472ccce58f2166ac058d9cf427ad7d74986e60a56d2fee0a8b680e466a8ea4e508a76c058b6f97b99c9aa5b10297b1a1bd6a8e80f3a79e008fa55a4a8915fbdec78b6b117ad67e195311fe79fc084c33f6db546f5b7602d010fa8b830e3f1b00cef00ee16840178fc7e9aa5f1cee625d43de8488bf6c8bd379ea6f97c55c7a9ee091477a23533d5e52e194bd9d4e17b02a64a2736feb3779fabd5777e448ffee0f2d4b38a8e7441822b882fc6df0bde8541e85c0c78a05936cff0c88a50980b7a84971fba3650991fe2cba425ac4b4289e7b06ce2cfabfcc8a553201e8c74b45e4ae74b6d054e37af95e6fd55e029b7c526b85ecfb3be8db670218ee3dda7b2a54ab1ed26eefe4cd1d2a9c589a6e94d0aa3ebe29e40e616aa0b731061c3d6e247ec610024a1a97b7adb7919308b0fb5dd5d51a58aa2f55d77b88037de7c1a74823c96cb09d22dd7f90dba14eefdcffaab34d323c829f24742f6f6b32b0724a26ae4a81130a8a275d30c21e6245fa27cf26d606a49bccba2980697c32d9efe583c4ee2140569025c4f044d744bc40cec1660d9e4d2de3a4de83bae4f0a9fdb34ef4509b2b4e6c37967a485a52d69d1573bb826bc64c966de9c792b7c2f07b645c56a29381911a98928e48516f246a55bcaa78f3c7d1c30127df5f06ba0a2d6a5e54605a20e60fab30c01a9472cb610ca0ef2418a985af00c7e47539111bf539dd554297d0374a7ff627d879600595b442c8dcffcffa3bbb07e5c7882ff0858142be4deac448698f0917fe2b7a9b686a9df1fa929f06a51aff992a6ee0b0605f8b34b87600cfa0af2475333b78625ce1520c793dc5080218247b4e41bbd7d9dab163470fe17a3d2622cdce979cc5565b0bc04eabaf656f21fa072a18ab33c656b665248ef20321407fef263b1c67316f2c6f236951990099e42d4614d8e08b27aa89d9f4548fa321d4b381d2da04fd7f17d6b9a68adfd0e4427196d25dcad869f8a155c6242f7d072baa5e7405ceb65dfaa3eb864bfe679a17df34273fde5037befe9ed5391b932cee271f59128c61ab3f0fc3f7cf8ff051fbda8382c64579efddd494c79850c56bda73bcd39c20c2820d191995b3335253c3b0ac8f5e5373f40c228886e6c526c2c249a5304578ba2a80f591c34ca1eaa84d6cc9399cf3f1207e61c4acada647e4e87ad5fba84aeeff6b6881d35bda77c74384fc5e279a0f495d509bc882c2b8bc790651a6d7a4ecba23a3f05111e1d8be37c03439fbd484668ceab69a52b7d519b169cbbcf634ee5e3bf78a5f8771f95fea03f2cb889e116a9f5de3abeacb8e42475fb5d022484b02d11f1e406332e0a773098fc4f0baa57cda2863c554f291d4eb74e63e4b3d44b0ed156bff1820003d407a3aaa9e6dfaa226ba7ef2fd0eff90a5482926f47f24f67019edccb6fd329eef30b5fb2125276aa1fe75a702b32c907ab133c72a74e77e0a5eb48fc5176b9d65b75b0038e1a9ed74ec2a3dcd2348fa54256f082abc01a301bacef7380f20ee0411c08a35dafdaae9f9fc123448da28626ffcc654e9d522bc8b8776b13a3310f7eeb4d27290ef4cbc7492fbcb5409d455748a8a1f087430cf5e6f453e2caa0c5343fcf4374cc38bead49941d8ab59b4d5181716c238aa88dbf1c4a2da3a9a9b9435d5ee1d51d27b0655a4308c1252aaf633cd8f44a351ffc8cec65de0b7e4e2556100e2ae9bc511044351109a6254b2d387b1a72c768f43fa7be6b93806e323b55c3e7925ed627dc708fde0954b299b1ca33bb7fbe33e0f9e4ce5b4f26efaf8e5b9507ada4f8658998eb7167afbd4482ee47cc60f4039d6a77c1fb126033bfc2e7c6162ff7561f22e263325c53a014a4ac9390fe6fab5d433c1e9896fe561f22fc8290f3f4560b676f3dfbfd1fe605343a0685349241b83a28d61cc0292d1f638a36d3d87bfa9f72f9df1cfe90692dfda5bd5e698362f5316984cbe73a132a801acbca76b5f5c23d98a217f2159b6cbbcdf8f52d23ea24c9471a31562a651b20e05cd0300ee500a450cfdaa4d2d83f7e7e27f8b7c793cf80f8067dadef77e49a64c373b97bac4dd472e5145072c73d0fdd68d9646c8a8ed9aec6c40bc915ae44ae27391ca0f1a4d2cb1c3d097be614e6eba807f4549d769a5872f268ccf770f2682d844490348f0b6a0d2b51aadbb5523cf708b66f9928eed12b35a39cf42d283b29f5283e1c8ba1f73457af17b14cdfdf9a85b0589acf1f9504e46b0bab8be848dac5673587035b99f56c41d3195bbba1616b149a22193cfb760d6bf2d84861653cd21be9a2d33187cb25d47fbecdd4626d1d97202f460a39b7128cadb77ddf682feca61fb6de0290df598a565a6361a91d76c0c685046489ed4cb1dcc4f1cea849c12dc4a3d38d3010567f387590532b78927e92f0b718c84e882b3df071a78a011d0fd56d4101dcb009914a16a781b240a6fb2440c72b0ffb365be9d3459d114e665a0d35d7b8bd280101d85d1211d939ba0b15ab528c4f9dd2b001172561d211671b96873010ae3c2b8317f773d735698914228764b831423ae19dd4bbb008b9f1bd1e3ebdd626e629a46a9dd70bdd4bb30e2279e83c12bbbead6479b5f9980b1a9c785395520703a9367d931b45c1566c9d314b1745cafc6d0667cc9bc94d0c53a960c829eb09b768ab6bb2133e4fea1d939f3d3f8e1237210cf3577c830f0493073dc1d189abf27402b8b31b7c172c43dbf331a0828adfe737380e763d0ab0bfaaf94ec04830f94380a83718f340c4eeb20d7eb22b94613be84a9ed332ab364efff6cb37eec35d186185cca725e7a748f6bdb427604fb1628d49a7424a5a62a2e930fe142b035503af332fe748d5e63591b9ac54071ca843d5e474a48837de8b80387f3269ab50d2fd99c08c971e015d13fa02c7c315922ce58bdacbf8ee48827851a61fca59882d7eadcce3166dfe012aa9ec849e698e776a4d384f4755b506a222636942a81bbbffa1ff47e4d81fe68120aebcfd1a7e0000fd0cffdc44e1f0cd69ea2b4936564c78af51fed1cc8e34f0b46d6330b4b50ddee09335b7b0be0bc9f7f8e48415e15d08f811653d21bc6dd152742b086caadcc6dff5e27b40da42c2f1ebf3dd2bd51c418718e499859239317fcab10892eadf1c0ebf7a4246bce4cce3617193032f3e41b977dc8650298ac39631c527460364effea0f0bfd043df72ead0406aba1bcd636d65d7b89979eb8e1",
    jump1e20  = "e172e20c5d2de26b567c0cace9e7c6cc4407bd5ffcd22ca59d37b73d54fdbd937cd3abc6f502e8c186dbd4f1a06b9e2b894f31be77424f94dddfd5a45888a84ca66eeeb242eefe6764ed859dafccae7a6a635b3a63fe9dfbbd5f2d3f2610d39388f53060e84edae75be4f4f2272c0f1f26d1231836ad040ab091550f8a3a5423fb3ab83e068fe2684057f15691c4dc757a3aee4bca8595bf1ad03500d9620a5dbe3b2d64380694895d2f379ca928238293ea267ce14236d5be816a61f018fe4f6bc3c9865f5d4d4186e320ab653d1f3c035ae83e2ad725648a67d3480331e763a1dcdfb5711b56796170b124f5febd723a664a2deefbfa9999d922a108b0e683582ae8d3baacb5bb56683405ea9e6e0d71ddb24b2229c72bb9d07061f2d1fa097ade823b607a2029d6e121ae09d93de01a154199e8e6a6e77c970bda72ba8079b2b3a15dd494a3188b1d94a25ae108a8a5bd0b050e6ce64a365a21420e07fdeebecae02eb68a4304b59283055d22c27d680ea35952834d828c9b9b9dd1a886b4f7fe82fe8f2a962e1e5390e563dc281c799aee2a441b7a813facb6ff5e94c059710dcfe7e6b1635e21ae0dc878dd5f7cc0e1101a74452495a67d23a2672c939f32c81d4a2611073990e92a084cc3a62fd42ee566f29d963a9cc5100ccd0a200f49ce0a74fa891efa1b974d342b7fedf9269e40d9b34e3c59c3d37201aecd5a04f4ae3d0c9a68c7ab78c662390e4cf36cb63ea3539c442efd0bf4aace4b8c8bde93c3d84b4d6290adfae1c5e3fcd457b6f3159e501f17b72ff6bc13d6bf61fbdafabefd16ac1dae0bca667e4e16a2b800732f1d0a9274c8a4c6cccd2db62fc275dc308c31c11cd6fda78de2f81f0e542b76b42b2cc09ed8f965d94c714c9918064f53af5379cfbbc31edf9cbce694f63a75f122048de6e57b094908f749661456813a908027f5d8397ab7962bf75ac779a3e1b7ae3fbc93397a67b486bb849befff1de6162ef2819715a88f41881e366ace692a900796a2806393898dd1750ac2b4ca3d34ca48942322fb6375f0c9a00c9701048ee8d7d7a17e11739177a7ad5027556e85835daf8594d84a97fe6621c0fce1495ae6ab8676cdc992d247acf5a4e5ec8c4755fde28117228d2c3ecf89edb91e93d949e2174924572265e36d176d082ed1be884e51d885ba3cda175c51edcee5042eaf519d292aa05aa4185b03858d710a9d0880b3d4e5111f858a52fe352cbe0a24f06a3d977ae2eb85e2a03a68131d0ab91dac4941067cf90ecd0fce156bcd40b8968cd4aa11e0b4353b14508d79d13ac00af4a4d452496b7f2393699889aa1e508427dbf0be3db91d955feb51e559af57640c6b3f9d5f95609852c28f9462a9869dd93acbdb1aafb2381ebb886a0b3fcec278f8bb0f62c23e157e49b89245b0881268ce594acbddd3605b9eaa77c9ff513e0dbad514914136d96fe2843fe2b4e886a0b718a9b8d1132132110618d0d3595da284cd2a4c9d09386199e4f4d7723983d3a374b51cf20dac5cabb4ff7e7197c2ebd9318463409baa583d6a6115c1b768282ff37b0fe152c97671e400d5ccba7d6875df0bf95c5d91257fedb124de393f31908d0e36251326aa29dd5be86291c80b4bf78f419ec151eeaeff643a58b48ab35ad2cd2c0b77b1965966ef3db6b6373cb2c4b590cef2f16f4d6f62f13a6cbf1a481565b5935edd4e76f7b6a8fd0d74bc336b40a803aec38125c006c877dfdcdb9ba2b7aecab5cafe6076e024c73e3567adf97f607a71d180402c22a20a8388f517484cc4198f97c2fe4f3407e0dc577e61f0f71354aa601cf4e3e42e1edd8722d50f5af3441f68caa568cc1c3a19956c1233f265bb47236afab24ee42b27b0042b90693d77c1923147360ae6503f6ba6abbc9dd52a7b4c36a3b6b55f6a80cfa7f101dd9f1bfc7d7eaf09a5d636b510228f245bfb37b4625025d2c911435cdf6f878113753e0804ab8ecab870ad733b9728d7636b17578b41239393e7de47cbce871137d2b61729dda67b2b84cd3363aad64c5dd5bd172f1f091305b1ff78982abe7dab1588036d097cf497e300e6c78a926048febd1b9462c07f5868928357b74297c87f503056b89f786d22a538b6702e290bca04639a0f1d0939b67f409e5e58e472a6a07fa543e2531c2567ec73c41f6769b6ba94c5aa0a030d006f5b6b1c5fb218b86a8f63a48bc867466f20f699859e87956f48a182d26ed451861dd21201ecc7239037ada67319bdf0849c387c73a110af798b4c5f9018bc97993e060ea2a2937fa2eb095d65ec07009fc407a350f1d6fb3c98a0a5f204be985b0cb6962f0eb7844a179c4598a92ea32d2d706c800034d2e960ded5b476d77073316b933fb3e6ba2f4f24a3b73a1e4d8ed1491d757ecf56fd72465dac0000736744d28d29073091587c8bccad302f7054e8a32bb8724974d9f3e449fc70b2a41f0008b548f717ac0a2c3a6580bfb50774933a578ad6acdcb89940bb406ea540893f097d8a88d1609ed605f25499de939083a0c8a7c6db462df5dfa06c298dd233e249433a54267d5cdc22e5524705b7d6b16b96bb2cb83e00cef62e21d91528a74cf95bfd1d391590c93f4058e9bb02656fd087a5b63d738d1c3b5cf533fd59c81cf9136bfcd3e955c19daf9906ef175791fde6a1d98155d7881e241c3522551cf9fcae42e1e46929ea39fd00943446823f9755085ccc8456a3090b73a3031a201d9c704a4ad4868dd9b6d06205560013973f60d637de2f18354bf4523d9d81dc2a7e78cd42c586364bbe0ed86fde0f081f801c1a4abb830839b7796d9a01f141bec8bd93144104c6dc59170162c0a5a639eb63a0a164970de50eb2e04f027394b26ed48d341f7851994df79d7cd663672a556f25e5e16a3adbe1003d631de938fabfed234df12b5ff3027f4a2da823834cb098e0f977a4eb9614579d5c7a1d400a1a933a657aef8ea1a66743d73b0cf37a7d64e9a63e4c7b09945f0db750b311b39783fb5ea216616751967d480a630d3da7c89d1c7beae20369137e96734a4cfedca56a7887f076fe4fe97534ad3e4f74d1a81750581a5ea214b440c7f30331ab86c257534c71175d1e731303a48b01c589fda4fb0d4368b4dd63d91204cb6fc389b2202aa94391907bfb72902a4031f5589ed5f391c2ce92aa998c200ba3c77d8bd747b9d0a29fa85cda3949a6d2bd0c3402e68f98fd451aa27b6c2dfd170e004577cbdb25e3a1b9852e9f66a370789c47bfce722446dade1b32ceae71ee0e1d96edf7ed08a93e3690056f46c3d8e63f88e53673ee71d72cfedbeba493ee91333120e09e9ce9f9c9a7a400f814ea618b1de48f9805e092f4e20f301fbb65caa83735a2a5c89befe4bce4116dca3688e1e14c6f09a945671dedbb5c0ba526842b6cae31d8b5ff978bae928a17a75c134630dd9de988f6ad3d89a071b33775a9660a40b48ec61ad3f93ac81cb1c65d8b0bab5c214786abd13cc10a8ea2e2a370e86e2fa1a372d83c9697b5e37b281e51507685f714fdaebe49ffc93a5582e1936eaee8e4140a4b72"
    D = Base.dSFMT
    @test D.GF2X(jump25000).z == D.get_jump(25000).z
    @test D.GF2X(jump1e20).z  == D.get_jump(big(10)^20).z

    # test PRNG jump
    mta, mtb = MersenneTwister(seed), MersenneTwister(seed)
    step = 25000*2
    size = 4
    mts = randjump(mta, size, jump25000)
    @test length(mts) == 4
    for x in (rand(mts[k], Float64) for j=1:step, k=1:size)
        @test rand(mtb, Float64) == x
    end
end
