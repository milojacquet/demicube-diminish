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
        vert := [1, 2, 5, 10];
        adj := [vert, [2, 5, 10, 15]];
        illegalc := [vert];
    else
        Error("invalid parameters");
    fi;
    PolyDiminish(G, vert, adj, illegalc);
end;

# Diminish an E8 polytope. k can be "a0", "a1", "a2", "a3", "b0", "b1", "c", or "m".
E8Diminish := function(k)
    local G, vert, adj, illegalc;
    G := Group(
        (  1,  2)(  3,  5)(  6,  8)(  9, 11)( 13, 15)( 18, 20)( 25, 27)( 44, 57)( 52, 65)( 56, 69)( 58, 71)( 60, 75)( 63, 78)( 64, 79)( 66, 80)( 67, 82)( 68, 83)( 70, 84)( 72, 86)( 73, 87)( 74, 91)
            ( 76, 92)( 77, 94)( 81, 95)( 85, 97)( 89, 99)( 90,101)( 93,105)(104,118)(111,123)(117,129)(124,135)(130,140)(133,144)(136,147)(141,152)(145,158)(148,162)(154,166)(156,171)(159,173)
            (161,176)(163,178)(169,181)(172,186)(175,188)(177,191)(179,192)(180,193)(187,201)(213,223)(221,227)(222,228)(224,229)(225,231)(226,232)(230,233), (  1,  3)(  2,  5)(  4,  7)( 17, 23)
            ( 22, 30)( 24, 33)( 29, 38)( 31, 41)( 34, 46)( 37, 48)( 39, 50)( 42, 54)( 47, 62)( 58, 72)( 66, 81)( 70, 85)( 71, 86)( 73, 90)( 76, 93)( 80, 95)( 84, 97)( 87,101)( 88,100)( 92,105)
            ( 96,107)( 98,109)(102,113)(103,115)(106,119)(112,125)(117,124)(121,127)(129,135)(133,136)(138,142)(144,147)(146,150)(148,156)(161,163)(162,171)(164,165)(168,184)(176,178)(179,180)
            (183,196)(185,199)(190,205)(192,193)(195,208)(197,211)(200,215)(204,217)(206,219)(216,220)(224,230)(229,233)(234,235), (  3,  6,  9, 13, 18, 25)(  5,  8, 11, 15, 20, 27)(  7, 10, 14, 19,
              26, 35)( 12, 17, 24, 34, 47, 36)( 16, 22, 31, 42, 28, 37)( 21, 29, 39)( 23, 32, 43, 55, 62, 48)( 30, 40, 51, 46, 61, 50)( 33, 45, 59, 54, 38, 49)( 41, 53)( 44, 58, 73, 68, 77, 63)
            ( 52, 66, 56, 70, 74, 67)( 57, 71, 87, 83, 94, 78)( 60, 76, 64)( 65, 80, 69, 84, 91, 82)( 72, 89, 90, 85, 93, 81)( 75, 92, 79)( 86, 99,101, 97,105, 95)( 88,103,116,128,139,151)
            ( 96,108,121,132,143,157)( 98,110,122,134,146,160)(100,112,113,109,119,107)(102,114,126,137,149,164)(106,120,131,142,155,170)(111,124,136,148,163,179)(115,127,138,150,165,125)
            (117,130,141,154,169,180)(123,135,147,162,178,192)(129,140,152,166,181,193)(133,145,159,175,161,177)(144,158,173,188,176,191)(153,168,185,200,194,207)(156,172,187)(167,183,197,203,202,216)
            (171,186,201)(174,190,206,182,195,209)(184,198,212,215,208,220)(189,204)(196,210,219)(199,214,211,217,205,218)(213,224,222,225,221,226)(223,229,228,231,227,232)(234,236,237,238,239,240), 
          (  1,  4)(  2,  5)(  3,  7)(  8, 12)( 11, 16)( 15, 21)( 17, 23)( 20, 28)( 22, 30)( 24, 33)( 27, 36)( 29, 38)( 31, 41)( 32, 44)( 34, 46)( 37, 48)( 39, 50)( 40, 52)( 42, 54)( 43, 56)( 45, 60)
            ( 47, 62)( 49, 63)( 51, 64)( 53, 67)( 55, 68)( 58, 72)( 59, 74)( 61, 77)( 66, 81)( 70, 85)( 71, 88)( 73, 90)( 76, 93)( 80, 96)( 84, 98)( 86,100)( 87,102)( 89,104)( 92,106)( 95,107)
            ( 97,109)( 99,111)(101,113)(103,117)(105,119)(112,125)(115,124)(118,123)(121,133)(127,136)(129,135)(138,148)(140,153)(142,156)(144,147)(146,161)(150,163)(152,167)(158,174)(162,171)
            (164,180)(165,179)(166,182)(168,184)(173,189)(176,178)(181,194)(183,196)(185,199)(186,202)(188,203)(190,205)(191,207)(192,193)(195,208)(197,211)(198,213)(200,215)(201,209)(204,217)
            (206,219)(210,221)(212,222)(214,225)(216,220)(218,226)(224,230)(229,234)(233,235)
    );
    if k = "a0" then
        vert := [1];
        adj := [[1], [2]];
        illegalc := [[1], [2], [7], [10], [14]];
    elif k = "a1" then
        vert := [1, 2];
        adj := [[1, 2], [1, 7]];
        illegalc := [vert];
    elif k = "a2" then
        vert := [1, 2, 7];
        adj := [[1, 2, 7], [1, 2, 10]];
        illegalc := [vert];
    elif k = "a3" then
        vert := [1, 2, 7, 10];
        adj := [[1, 2, 7, 10], [1, 2, 7, 14]];
        illegalc := [vert];
    elif k = "b0" then
        vert := [1, 2, 3, 5, 10, 12, 14, 16, 19, 21, 26, 28, 35, 36];
        adj := [vert, [2, 5, 12, 14, 21, 28, 36, 75, 82, 83, 94, 98, 109, 123]];
        illegalc := Set(Concatenation(adj, [[1, 2, 12, 16, 21, 28, 36, 100, 107, 109, 111, 113, 119, 123]]));
    elif k = "b1" then
        vert := [2, 5, 12, 14, 21, 28, 36];
        adj := [vert, [2, 12, 21, 28, 36, 109, 123]];
        illegalc := [vert];
    elif k = "c" then
        vert := [1, 2, 7, 10, 14, 19, 26, 35];
        adj := [vert, [1, 2, 7, 10, 14, 34, 42, 47]];
        illegalc := adj;
    elif k = "m" then
        vert := [1, 2, 7, 10, 14];
        adj := [[1, 2, 7, 10, 14], [1, 2, 7, 10, 19]];
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
