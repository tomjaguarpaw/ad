`mySumMTL` optimizes to this excellent loop:

```
Rec {
$wgo3
  = \ x_s3Te ww_s3Th ->
      case x_s3Te of wild_X1H {
        __DEFAULT -> $wgo3 (+# wild_X1H 1#) (+# ww_s3Th wild_X1H);
        10# -> +# ww_s3Th 10#
      }
end Rec }
```

`mySumEff` "optimizes" to this bad loop.  For some reason it doesn't
feel the need to lift the `\ eta2_a27m` to the top of the function
definition.

```
Rec {
mySumEff_go3
  = \ x_a3Pi ->
      let {
        k_a2XS
          = case x_a3Pi of wild_X1H {
              __DEFAULT -> mySumEff_go3 (+# wild_X1H 1#);
              10# -> n_r3Vj `cast` <Co:66> :: ...
            } } in
      (\ eta2_a2Zm ->
         case eta2_a2Zm of { I# x1_a35s ->
         (k_a2XS `cast` <Co:39> :: ...) (I# (+# x1_a35s x_a3Pi))
         })
      `cast` <Co:44> :: ...
end Rec }
```
