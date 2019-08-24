# Loop2, A Mathematica Package for Textbook-Level Loop Calculation

## Usage
- One loop calculation
```
OneLoop[denor,nor,k,exm,dim], 
```
i.e. 

$$
\int\mathrm{d}^dk\frac{k2}{(\mathbf{k}-\mathbf{p})^2(\mathbf{k}^2-m^2)}
$$

```
OneLoop[{{k-p},{k,m^2}},k2,k,p,d]
```
- Two loop calculation
```
TwoLoop[denor1,denor2,nor,k1,k2,exm,dim], \n i.e. TwoLoop[{{k2-k1,1},{k2,2mE,1}},{{k1-p,1},{k1,2mE,2}},k1^4,k2,k1,p,d]
```
- Convenient Integration alias
```
LoopIntegrate[integrand,Assumptions->{}]
```
