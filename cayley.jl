module cayley

using Grassmann
using Formatting

# this file is about euclidean 3-space
@basis "+++"

# NB using the Grassmann algebra we easily get the binary groups too
# (but how do we visualize these?)

# using AbstractAlgebra
# using DataStructures

# A group element (relative to a generating set and representation)
# is a word in generators and their inverses and the representing clifford elt
CliffordElt = MultiVector{V,Float64,8}
ThreeVector = Chain{V,1,Float64,3}
GroupElt = Tuple{String, CliffordElt}
Edge = Tuple{ThreeVector, ThreeVector}
Face = Vector{ThreeVector}
# a group is a vector of group elements
Group = Vector{GroupElt}

function printgroup(G::Group)
    for (w, g) in G
        println("word $w represents $g")
    end
end

function getelt(default::Function, G::Group, g::CliffordElt)
    for (w, h) in G
        if h ≈ g || h ≈ -g
            return w::String
        end
    end
    return default()
end

function getvertex(default::Function, L::Vector{ThreeVector}, P::ThreeVector)
    for Q in L
        if (0.0v + P) ≈ (0.0 + Q)
            return Q::ThreeVector
        end
    end
    return default()
end

Base.isapprox(e::Edge, f::Edge) = (
((0.0v + e[1]) ≈ (0.0v + f[1]) && (0.0v + e[2] ≈ 0.0v + f[2]))
|| ((0.0v + e[1]) ≈ (0.0v + f[2]) && (0.0v + e[2] ≈ 0.0v + f[1])))

function getedge(default::Function, L::Vector{Edge}, e::Edge)
    for f in L
        if e ≈ f
            return f::Edge
        end
    end
    return default()
end

Base.isapprox(X::Face, Y::Face) =
    let N=length(X)
        ((N == length(Y))
         && (any(i ->
                 all(j -> (0.0v + X[j]) ≈ (0.0v + Y[1+(i+j)%N]), 1:N), 1:N)))
    end

function getface(default::Function, L::Vector{Face}, X::Face)
    for Y in L
        if X ≈ Y
            return Y::Face
        end
    end
    return default()
end

function mkeuclgp(a::CliffordElt, b::CliffordElt;
                  bound::Int=10) :: Group
    worklist::Group = [("", 1.0v+0.0v₁)]
    G::Group = []
    A = ~a # we assume clifford elements are normal
    B = ~b
    while ! isempty(worklist)
        @inbounds (w, g) = popfirst!(worklist)
        if length(w) > bound
            continue
        end
        getelt(G, g) do
            push!(G, (w, g))
            push!(worklist, ('a'*w, a*g), ('b'*w, b*g), ('A'*w, A*g), ('B'*w, B*g))
        end

    end
    return G
end

function rotor(degree::Float64, vector::ThreeVector)::CliffordElt
    return exp(-π/degree*(⋆(vector/norm(vector))))
end

function apply(a::CliffordElt, v::ThreeVector)::ThreeVector
    return (a*v*(~a))(1)
end

function showvertex(v::ThreeVector; precision::Int=5)::String
    fs = FormatSpec(".$precision"*'f')
    return ("(" * fmt(fs, getindex(v,1)) * ", "
                * fmt(fs, getindex(v,2)) * ", "
                * fmt(fs, getindex(v,3)) * ")")
end

## Some example: a cyclic and a dihedral group
turn = rotor(5.0, 0.0v₁+1.0v₃)
flip = rotor(2.0, 1.0v₁+0.0v₃)
C5 = mkeuclgp(turn, turn)
D5 = mkeuclgp(turn, flip)

# generators of A5
# 1/5 turn around P
# 1/2 turn around edge PQ
ϕ = .5*(sqrt(5)+1.0) # golden ratio
P = +1.0v₂ + ϕ*v₃
Q = -1.0v₂ + ϕ*v₃
a = rotor(5.0, P)
b = rotor(2.0, P+Q)

A5 = mkeuclgp(a,b)

# cube and tetrahedron
N = 1.0v₁ + 1.0v₂ + 1.0v₃
M = -1.0v₁ - 1.0v₂ + 1.0v₃
K = -1.0v₁ + 1.0v₂ + 1.0v₃
d = rotor(3.0,N)
c = rotor(2.0,N+K)
A4 = mkeuclgp(d,b)
S4 = mkeuclgp(d,c)

"""
Make a TikzPicture of a platonic solid
P and Q are two adjecent vertices,
degree is the number of faces around a vertex
"""
function drawplatonic(degree::Float64, P::ThreeVector, Q::ThreeVector)
    a = rotor(degree, P)
    b = rotor(2.0, P+Q)
    G = mkeuclgp(a,b)
    vertices::Vector{ThreeVector} = [P, Q]
    edges::Vector{Edge} = [(P, Q)]
    face1::Face = [P, Q]
    # complete the first face, iterating b*a
    for i in 1:10
        R = apply(b*a,last(face1))
        getvertex(face1, R) do
            push!(face1, R)
        end
    end
    faces::Vector{Face} = [face1]
    # find all vertices, edges and faces, iterating over G
    for (w, g) in G
        P₁ = apply(g,P)
        Q₁ = apply(g,Q)
        getvertex(vertices, P₁) do
            push!(vertices, P₁)
        end
        getedge(edges, (P₁,Q₁)) do
            push!(edges, (P₁,Q₁))
        end
        newface = apply.(Ref(g),face1)
        getface(faces, newface) do
            push!(faces, newface)
        end
    end
    tikzstring::String = ""
    for X in faces
        tikzstring *= "\\fill "
        for R in X
            tikzstring *= showvertex(R) * " -- "
        end
        tikzstring *= "cycle;\n"
    end
    for (P₁,Q₁) in edges
        tikzstring *= "\\draw " * showvertex(P₁) * " -- " * showvertex(Q₁) * ";\n"
    end
    return tikzstring
end

## Some examples to try
# drawplatonic(3.0, N, M) # tetrahedron
# drawplatonic(3.0, N, K) # cube
print(drawplatonic(5.0, P, Q)) # icosahedron

"""
Make a TikZpicture of a cayley diagram of a platonic solid
P and Q are two adjecent vertices,
degree is the number of faces around a vertex
"""
function drawcayley(degree::Float64, P::ThreeVector, Q::ThreeVector)
    tikzstring::String = ""
    a = rotor(degree, P)
    b = rotor(2.0, P+Q)
    A = ~a
    B = ~b
    G = mkeuclgp(a,b)
    for (w, g) in G
        tikzstring *= ("\\node[vertex] (n" * w * ") at "
                       * showvertex(apply(g,3.0/4.0*P+1.0/4.0*Q)) * " {};\n")
    end
    for (w, g) in G
        aw = getelt(G, g*A) do
            "error"
        end
        bw = getelt(G, g*B) do
            "error"
        end
        tikzstring *= "\\draw[gena] (n" * w * ") -- (n" * aw * ");\n"
        tikzstring *= "\\draw[genb] (n" * w * ") -- (n" * bw * ");\n"
    end
    return tikzstring
end

end
