# Mind map of file dependencies

Only imports between files of this project are shown (Mathlib is omitted).
An arrow `A --> B` means "A imports B". `CMAbelianVarieties.lean` imports every file below except `Test`.

> **How to view this as a picture (VS Code):** open this file and press
> **`Ctrl + Shift + V`** to see the rendered diagram.

```mermaid
graph TD
  %% ---------- top level ----------
  Theorem["<b>Theorem</b><br/><i>main theorem: CM abelian varieties have models over number fields</i>"]
  Defn["<b>Defn</b><br/><i>CMStructure, F-module ℚ ⊗ lattice ≅ F, u_ℝ : ℝ ⊗ F ≅ Lie A, complex structure J, CMType</i>"]

  %% ---------- AbstractNonsense ----------
  subgraph AN["AbstractNonsense/"]
    direction TB
    IntHomAN["<b>IntHom</b><br/><i>[n] on group objects</i>"]
    PullbackAddGrp["<b>PullbackAddGrp</b><br/><i>group structure on pullbacks</i>"]
    EndBaseChange["<b>EndBaseChange</b><br/><i>End G →ₐ[ℤ] End (F.obj G)</i>"]
    EndRingIso["<b>EndRingIso</b><br/><i>G ≅ H ⇒ End G ≃+* End H</i>"]
  end

  %% ---------- AlgebraicGeometry ----------
  subgraph AG["AlgebraicGeometry/"]
    direction TB
    Finite["<b>Finite</b><br/><i>finite over a field ⇒ Artinian</i>"]
    InvertibleSheaf["<b>InvertibleSheaf</b><br/><i>line bundles</i>"]
    TheCube["<b>TheCube</b><br/><i>theorem of the cube</i>"]
    AGBasic["<b>Basic</b><br/><i>base change X _ K₁ (+ instances), base change of open covers, proper ⇒ quasi-compact</i>"]
    AGDimension["<b>Dimension</b><br/><i>dim X = sup of dim 𝒪_{X,x} / over an open cover; dim X = dim (X _ K₁) under base change</i>"]
    subgraph RM["RationalModel/"]
      direction TB
      RMAffine["<b>Affine</b><br/><i>affine X of finite type over K̄ has a model over a finite E/K</i>"]
      RMSeparated["<b>Separated</b><br/><i>same for separated X, by gluing affine models</i>"]
      RMMorphism["<b>Morphism</b><br/><i>the model is proper / geometrically integral</i>"]
      RMGroupStructure["<b>GroupStructure</b><br/><i>group structures descend to a field of definition</i>"]
    end
    subgraph LIE["LieAlgebra/"]
      LieAlgebra["<b>Defn</b><br/><i>Lie G, End G acts on Lie G and on ℂ ⊗ Lie G</i>"]
      Dimension["<b>Dimension</b><br/><i>dim Lie G vs dim 𝒪_{G,e}</i>"]
    end
    AGCatalogue["<b>Catalogue</b><br/><i>#check cheat sheet</i>"]
    subgraph AV["AbelianVarieties/"]
      direction TB
      GlobalSections["<b>GlobalSections</b><br/><i>Γ(A) ≅ K</i>"]
      TateModule["<b>TateModule</b><br/><i>torsion points, Tate module</i>"]
      AVRationalModel["<b>RationalModel</b><br/><i>an abelian variety over K̄ has a model over a finite E/K</i>"]
      AVCatalogue["<b>Catalogue</b><br/><i>#check cheat sheet</i>"]
      Commutativity["<b>Commutativity</b> ★<br/><i>abelian varieties are commutative</i>"]
      Complex["<b>Complex</b><br/><i>complex abelian varieties: exp, lattice, ℝ ⊗ lattice ≅ Lie A, free of rank 2g</i>"]
      subgraph HOM["Homomorphisms/"]
        direction TB
        EndomorphismRing["<b>EndomorphismRing</b><br/><i>End A, End A ⊗ ℚ</i>"]
        FiniteGen["<b>FiniteGen</b><br/><i>Hom(A, B) finitely generated</i>"]
        TorsionFree["<b>TorsionFree</b><br/><i>Hom(A, B) torsion free</i>"]
        IntHomAV["<b>IntHom</b><br/><i>[n], A[n] finite & discrete</i>"]
        Integral["<b>Integral</b><br/><i>End⁰ A as fractions of End A; integral elements</i>"]
      end
    end
  end

  %% ---------- ForMathlib ----------
  subgraph FM["ForMathlib/"]
    Endomorphism["<b>Endomorphism</b><br/><i>End G is a (semi)ring</i>"]
    FunctorCommAddObj["<b>FunctorCommAddObj</b><br/><i>F preserves comm. add. monoid objects</i>"]
  end

  %% ---------- preCMType ----------
  subgraph CM["preCMType/"]
    direction TB
    CMDefn["<b>Defn</b><br/><i>preCMType, preCMType from a complex structure</i>"]
    CMAlgebra["<b>Algebra</b><br/><i>background for CM types</i>"]
  end

  %% ---------- Algebra ----------
  subgraph ALG["Algebra/"]
    direction TB
    CMField["<b>CMField</b><br/><i>ℝ ⊗[ℚ] F for a CM field F, via complex embeddings</i>"]
    FieldRepresentations["<b>FieldRepresentations</b><br/><i>V = ⊕ V_σ for F →+* End_ℂ V</i>"]
  end

  %% ---------- Test ----------
  subgraph T["Test/ (top level, outside the library)"]
    Test["<b>Test</b><br/><i>scratch</i>"]
    Test1["<b>Test1</b><br/><i>scratch, Mathlib only</i>"]
  end

  %% ---------- imports ----------
  Theorem --> Defn
  Theorem --> AVRationalModel
  Defn --> EndomorphismRing
  Defn --> CMDefn
  Defn --> AGDimension
  AGDimension --> AGBasic
  Defn --> EndBaseChange
  Defn --> Complex
  AGBasic --> FunctorCommAddObj
  AVRationalModel --> RMGroupStructure
  AVRationalModel --> RMMorphism
  RMMorphism --> RMSeparated
  RMSeparated --> RMAffine
  RMAffine --> AGBasic
  RMGroupStructure --> AGBasic
  EndBaseChange --> Endomorphism
  EndBaseChange --> FunctorCommAddObj
  EndomorphismRing --> Commutativity
  EndomorphismRing --> EndRingIso
  EndRingIso --> Endomorphism
  FiniteGen --> Commutativity
  Integral --> EndomorphismRing
  Complex --> Dimension
  Complex --> Commutativity
  TateModule --> IntHomAV
  TorsionFree --> GlobalSections
  TorsionFree --> IntHomAV
  IntHomAV --> IntHomAN
  IntHomAV --> PullbackAddGrp
  IntHomAV --> Finite
  IntHomAV --> Commutativity
  IntHomAN --> Endomorphism
  LieAlgebra --> Endomorphism
  Dimension --> LieAlgebra
  FieldRepresentations --> CMField
  CMDefn --> CMField
  Test --> Defn

  %% ---------- colours ----------
  classDef goal fill:#fde2e4,stroke:#c0392b,stroke-width:2px,color:#000
  classDef hub fill:#fff3bf,stroke:#e67700,stroke-width:3px,color:#000
  classDef connected fill:#e7f5ff,stroke:#1c7ed6,color:#000
  classDef unused fill:#f1f3f5,stroke:#adb5bd,stroke-dasharray:4 3,color:#495057

  class Theorem goal
  class Commutativity hub
  class EndomorphismRing,FiniteGen,IntHomAV,Complex,TorsionFree,TateModule,GlobalSections,IntHomAN,PullbackAddGrp,Finite,Endomorphism,LieAlgebra,CMDefn,Test,AGBasic,AVRationalModel,RMAffine,RMSeparated,RMMorphism,RMGroupStructure,EndBaseChange,FunctorCommAddObj,Defn,EndRingIso,Dimension,Integral,AGDimension,CMField,FieldRepresentations connected
  class AVCatalogue,InvertibleSheaf,TheCube,AGCatalogue,CMAlgebra,Test1 unused
```

**Legend**

| Colour | Meaning |
|---|---|
| Red, thick border | the main goal (`Theorem`) |
| Yellow, thick border ★ | the hub (`Commutativity`, imported by 4 files) |
| Blue | part of the dependency chain |
| Grey, dashed | not connected to the rest yet |
