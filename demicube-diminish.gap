PolyDiminish := function(G, vert, adj, illegalc)
    local verts, adjacent, illegalcs, seen, isDiminishment;
    verts := Orbit(G, vert, OnSets);
    adjacent := Set(Orbit(G, adj, OnSetsSets));
    # one vertex is assumed to be present
    illegalcs := Orbit(G, illegalc, OnSetsSets);
    seen := [];

    isDiminishment := function(H)
        local vos, anygood, keepi, checki, good, v, adjs, canon, sym;
        vos := OrbitsDomain(H, verts, OnSets);
        anygood := false;
        # for one representative vertex in each orbit, check whether not diminishing one other orbit gives an illegal configuration
        for keepi in [1..Length(vos)] do
            if Length(vos[keepi]) = Length(verts) then
                anygood := true;
                break;
            fi;
            good := true;
            for checki in [1..Length(vos)] do
                if checki = keepi then continue; fi;
                v := vos[checki][1];
                adjs := Difference(Filtered(verts, w -> Set([v, w]) in adjacent), vos[keepi]);
                if ForAny(illegalcs, c -> IsSubset(adjs, c)) then
                    good := false;
                    break;
                fi;
            od;
            if not good then continue; fi;
            anygood := true;
            canon := Minimum(Orbit(G, Set(vos[keepi]), OnSetsSets));
            if not (canon in seen) then
                AddSet(seen, canon);
                sym := Stabilizer(G, Set(vos[keepi]), OnSetsSets);
                Print(Length(vos[keepi]), " vertices (order ", Size(sym), "): ", vos[keepi][1], " with ", GeneratorsOfGroup(H), "\n");
            fi;
        od;
        return anygood;
    end;

    LowLayerSubgroups(G, 1000, isDiminishment);
end;

# Diminish the n-demicube
DnDiminish := function(n)
    local gens, G, vert, adj, illegalc;
    if not (n >= 4) then Error("invalid parameters"); fi;
    gens := Concatenation([(1,n+2)(2,n+1)], List([1..n-1], i -> (i,i+1)(i+n,i+n+1)));
    G := Group(gens);
    vert := [1..n];
    adj := Set([vert, Set(vert+[n,n])]);
    illegalc := Set([Set(vert+[n,n]), Set(vert+[n,0,n])]);
    PolyDiminish(G, vert, adj, illegalc);
end;

# Diminish the k-rectified n-simplex for k ≥ 1
AnDiminish := function(n, k)
    local G, vert, adj, illegalc;
    if not (n >= 3 and k >= 1 and k < n/2) then Error("invalid parameters"); fi;
    G := SymmetricGroup(n+1);
    vert := [1..k+1];
    adj := Set([vert, Set(vert+[k+1])]);
    illegalc := [vert];
    PolyDiminish(G, vert, adj, illegalc);
end;

# Diminish the mesorectified n-simplex
Anx2Diminish := function(n)
    local gens, G, vert, adj, illegalc;
    if not (n >= 3 and n mod 2 = 1) then Error("invalid parameters"); fi;
    gens := Concatenation([Product([1..n+1], i -> (i,i+n+1))], List([1..n], i -> (i,i+1)(i+n+1,i+n+2)));
    G := Group(gens);
    vert := Concatenation([1..(n+1)/2], [(n+1)*3/2+1..(n+1)*2]);
    adj := Set([vert, Concatenation([2..(n+1)/2+1], [n+2], [(n+1)*3/2+2..(n+1)*2])]);
    illegalc := [vert];
    PolyDiminish(G, vert, adj, illegalc);
end;

# Diminish the k-rectified n-orthoplex for k ≥ 1
BnDiminish := function(n, k)
    local gens, G, vert, adj, illegalc;
    if not (n >= 3 and k >= 1 and k <= n-3) then Error("invalid parameters"); fi;
    gens := Concatenation([(1,n+1)], List([1..n-1], i -> (i,i+1)(i+n,i+n+1)));
    G := Group(gens);
    vert := [1..k+1];
    adj := Set([vert, Set(vert+[k+1])]);
    illegalc := [vert];
    PolyDiminish(G, vert, adj, illegalc);
end;

# Diminish an E6 polytope. k can be "a0", "a1", "c", or "m".
E6Diminish := function(k)
    local G, vert, adj, illegalc;
    G := Group(
        (1,4,21,6,7)(2,26,17,11,20)(3,19,9,13,14)(8,16,27,10,22)(12,24,18,23,25),
        (1,19)(2,18,16,10)(3,6,7,14)(4,9)(8,12,15,24)(11,23,26,17)(13,21)(20,27,22,25),
        (1,18,2,19)(3,7,24,8)(4,23,11,9)(5,15,14,12)(10,16)(13,21,25,22)(17,26)(20,27)
    );
    if k = "a0" then
        vert := [1];
        adj := [[1], [2]];
        illegalc := [[2], [3], [6]];
    elif k = "a1" then
        vert := [1, 2];
        adj := [[1, 2], [1, 3]];
        illegalc := [vert];
    elif k = "c" then
        vert := [4, 6, 11, 18, 24, 25];
        adj := [[1, 2, 6, 23, 24, 25], vert];
        illegalc := adj;
    elif k = "m" then
        vert := [1, 2, 3];
        adj := [vert, [1, 2, 6]];
        illegalc := [vert];
    else
        Error("invalid parameters");
    fi;
    PolyDiminish(G, vert, adj, illegalc);
end;

# Diminish an E6 polytope. k can be "c" or "m".
E6x2Diminish := function(k)
    local gens, invert, invertv, vert, adj, illegalc;
    gens := [
        (1,4,21,6,7)(2,26,17,11,20)(3,19,9,13,14)(8,16,27,10,22)(12,24,18,23,25),
        (1,19)(2,18,16,10)(3,6,7,14)(4,9)(8,12,15,24)(11,23,26,17)(13,21)(20,27,22,25),
        (1,18,2,19)(3,7,24,8)(4,23,11,9)(5,15,14,12)(10,16)(13,21,25,22)(17,26)(20,27)
    ];
    invert := Product([1..27], i -> (i,i+27));
    invertv := v -> List(v, i -> i^invert);
    G := Group(Concatenation([invert], List(gens, g -> g * g^invert)));
    if k = "c" then
        vert := Concatenation([4, 6, 11, 18, 24, 25], invertv([9, 14, 15, 16, 17, 20]));
        adj := [Concatenation([1, 2, 6, 23, 24, 25], invertv([10, 14, 15, 19, 20, 26])), vert];
        illegalc := adj;
    elif k = "m" then
        vert := Concatenation([1, 2, 3], invertv([18, 20, 26]));
        adj := [vert, Concatenation([1, 2, 6], invertv([10, 20, 26]))];
        illegalc := [vert];
    else
        Error("invalid parameters");
    fi;
    PolyDiminish(G, vert, adj, illegalc);
end;

# Diminish an E7 polytope. k can be "a0", "a1", "a2", "b0", "b1", "c", or "m".
E7Diminish := function(k)
    local G, vert, adj, illegalc;
    G := Group(
        (1,2,5,10,15,20)(3,7,12,16,21,6)(4,9,14,19,28,11)(8,13,18,25,33,29)(17,23,32,41,50,39)(22,30,24,27,37,49)(26,36,47,34,43,42)(31,40)(35,45,52,38,51,46)(44,48,53,54,55,56),
        (1,3)(2,6)(8,9)(14,17)(18,26)(19,22)(25,34)(28,29)(32,42)(37,43)(44,46)(48,51),
        (1,4,9)(2,5,11)(3,8,7)(12,17,24)(16,22,31)(18,27,38)(21,29,39)(25,35,46)(32,40,52)(34,44,47)(36,48,53)(37,50,45)
    );
    if k = "a0" then
        vert := [1];
        adj := [[1], [2]];
        illegalc := [[1], [2], [5], [10]];
    elif k = "a1" then
        vert := [1, 2];
        adj := [[1, 2], [1, 5]];
        illegalc := [vert];
    elif k = "a2" then
        vert := [1, 2, 5];
        adj := [[1, 2, 5], [1, 2, 10]];
        illegalc := [vert];
    elif k = "b0" then
        vert := [1, 2, 3, 5, 6, 7, 10, 12, 15, 16, 20, 21];
        adj := [vert, [3, 4, 5, 6, 8, 10, 11, 15, 17, 20, 22, 29]];
        illegalc := Set(Concatenation(adj, [[1, 3, 4, 7, 8, 9, 10, 13, 15, 20, 23, 30]]));
    elif k = "b1" then
        vert := [3, 5, 6, 10, 15, 20];
        adj := [[1, 3, 7, 10, 15, 20], vert];
        illegalc := [vert];
    elif k = "c" then
        vert := [1, 2, 5, 10, 15, 21, 25];
        adj := [vert, [1, 2, 5, 10, 15, 25, 28]];
        illegalc := adj;
    elif k = "m" then
        vert := [1, 2, 5, 10, 15, 25];
        adj := [vert, [2, 5, 10, 15, 21, 25]];
        illegalc := [vert];
    else
        Error("invalid parameters");
    fi;
    PolyDiminish(G, vert, adj, illegalc);
end;

ToCoords := function(n, vert, gens)
    local toVec;
    toVec := function(i)
        if i <= n then
            return IdentityMat(n)[i];
        else
            return -IdentityMat(n)[i-n];
        fi;
    end;
    return List(Orbit(Group(gens), vert, OnSets), v -> Sum(v, toVec));
end;
