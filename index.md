---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: default
---
<!-- # Loop2, A Mathematica Package for Textbook-Level Loop Calculation -->
This package is default to operate under 3-dimensional space, while the time component is integrated out. 
## Usage
- One loop calculation
{% raw %}
```
OneLoop[denor,nor,k,exm,dim], 
```
{% endraw %}
i.e. for

$$\begin{align}
\int\mathrm{d}^dk\frac{k_2}{(\mathbf{k}-\mathbf{p})^2(\mathbf{k}^2-m^2)}
\end{align}
$$

the following is used:
{% raw %}
```
OneLoop[{{k-p},{k,m^2}},k2,k,p,d]
```
{% endraw %}
- Two loop calculation
{% raw %}
```
TwoLoop[denor1,denor2,nor,k1,k2,exm,dim], \n i.e. TwoLoop[{{k2-k1,1},{k2,2mE,1}},{{k1-p,1},{k1,2mE,2}},k1^4,k2,k1,p,d]
```
{% endraw %}
- Convenient Integration alias
{% raw %}
```
LoopIntegrate[integrand,Assumptions->{}]
```
{% endraw %}
