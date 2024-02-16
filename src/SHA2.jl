module SHA2

export sha256, sha512

const parameter_variants = (;
    sha256 = (4, 8, 64, ((2, 13, 22), (6, 11, 25), (7, 18, 3), (17, 19, 10))),
    sha512 = (8, 16, 80, ((28, 34, 39), (14, 18, 41), (1, 8, 7), (19, 61, 6))),
)

#! format: off
const (H₀, K₀) = (
    (
        0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
        0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
    ),
    (
        0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
        0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
        0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
        0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
        0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
        0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
        0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
        0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
        0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
        0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
        0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
        0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
        0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
        0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
        0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
        0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
        0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
        0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
        0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
        0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
    ),
)
#! format: on

Ch(x, y, z) = (x & y) ⊻ (~x & z)
Maj(x, y, z) = (x & y) ⊻ (x & z) ⊻ (y & z)

Σ(a, b, c, x) = S(a, x) ⊻ S(b, x) ⊻ S(c, x)
σ(a, b, c, x) = S(a, x) ⊻ S(b, x) ⊻ x >> c

S(r, x::T) where {T} = x >> r ⊻ x << (8sizeof(T) - r)

for (γ, δ, rounds, (Ξ₀, Ξ₁, ξ₀, ξ₁)) ∈ parameter_variants
    (Γ, Δ, φ) = (8γ, 8δ, 8δ ÷ γ)

    @eval IntType = $(Symbol(:UInt, Γ))
    @eval SizeType = $(Symbol(:UInt, Δ))

    H = IntType.(H₀ .>> (64 - Γ))
    K = IntType.(K₀ .>> (64 - Γ))[1:rounds]

    SHAState = Symbol(:SHA, 8Γ, :State)
    sha = Symbol(:sha, 8Γ)

    init_digest = (
        quote
            X[$j] = $x
        end for (j, x) ∈ enumerate(H)
    )
    extend_words = (
        quote
            W[$j] =
                (σ($ξ₁..., W[$(j - 2)]) + W[$(j - 7)]) +
                (σ($ξ₀..., W[$(j - 15)]) + W[$(j - 16)])
        end for j ∈ (φ + 1):rounds
    )
    load_digest = (
        quote
            $x = X[$j]
        end for (j, x) ∈ enumerate((:a, :b, :c, :d, :e, :f, :g, :h))
    )
    scramble_words = (
        quote
            T₁ = h + Σ($Ξ₁..., e) + Ch(e, f, g) + $(K[j]) + W[$j]
            T₂ = Σ($Ξ₀..., a) + Maj(a, b, c)
            (a, b, c, d, e, f, g, h) = (T₁ + T₂, a, b, c, d + T₁, e, f, g)
        end for j ∈ 1:rounds
    )
    update_digest = (
        quote
            X[$j] += $x
        end for (j, x) ∈ enumerate((:a, :b, :c, :d, :e, :f, :g, :h))
    )
    run_rounds = (
        quote
            $(extend_words...)
            $(load_digest...)
            $(scramble_words...)
            $(update_digest...)
        end
    )

    @eval begin
        struct $SHAState
            digest::Vector{$IntType}
            words::Vector{$IntType}

            function $SHAState()
                new(Vector{$IntType}(undef, $(length(H))), Vector{$IntType}(undef, $rounds))
            end
        end

        function $sha(message::AbstractVector{UInt8})
            digest!($SHAState(), message)
        end

        function digest!(state::$SHAState, message::AbstractVector{UInt8})
            reinterpret(UInt8, digest_integers!(state, message))
        end

        function digest_integers!(state::$SHAState, message::AbstractVector{UInt8})
            (M, X, W) = (message, state.digest, state.words)

            m = length(M)
            nγ = m ÷ $γ
            mγ = nγ * $γ
            nγφ = nγ ÷ $φ * $φ

            M̂ = reinterpret($IntType, view(M, 1:mγ))

            @inbounds begin
                $(init_digest...)

                for k ∈ 1:($φ):nγφ
                    for i ∈ 1:($φ)
                        W[i] = hton(M̂[k + i - 1])
                    end
                    $run_rounds
                end

                j = nγ - nγφ
                for i ∈ 1:j
                    W[i] = hton(M̂[nγφ + i])
                end

                j += 1
                W[j] = 0
                for i ∈ (mγ + 1):m
                    W[j] = (W[j] + M[i]) << 8
                end
                W[j] = (W[j] + 0x80) << 8mod(-m - 1, $γ)

                j += 1
                if j + $(δ ÷ γ) > $(φ + 1)
                    W[j:($φ)] .= 0
                    $run_rounds
                    j = 1
                end

                # Here we'll assume δ/γ = Δ/Γ = 2.
                W[j:($(φ - 2))] .= 0
                W[$(φ - 1)] = (8m >> $Γ) % $IntType
                W[$φ] = 8m % $IntType
                $run_rounds

                map!(ntoh, X, X)
            end
        end
    end
end

end # module
