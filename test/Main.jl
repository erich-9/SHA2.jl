import SHA, SHA2

@testset "Main.jl" begin
    data = rand(UInt8, rand(0:100_000))

    @test SHA.sha256(data) == SHA2.sha256(data)
    @test SHA.sha512(data) == SHA2.sha512(data)
end
