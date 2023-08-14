# Competitive Gradient Optimization
## Description
### Code illustrating the Competitive Gradient Optimization algorithm introduced in [Competitive Gradient Optimization[PMLR:ICML]](https://proceedings.mlr.press/v202/vyas23a.html) [[arxiv]](https://arxiv.org/abs/2205.14232)
## Requirements 
### numpy==1.16.5
### matplotlib==3.1.1
## Illustrations

These are some examples of non-convex non-concave functions for which the CGO algorithm finds the saddle points for some choice of parameter alpha.

$x^2y$ : Shrinking region with increasing $\alpha$

![alt-text](https://github.com/AbhijeetiitmVyas/CompetitiveGradientOptim/blob/main/Shrinkning%20Region.gif)

$x^2y+xy$ : Convergence to Nash with large $\alpha$

![alt-text](https://github.com/AbhijeetiitmVyas/CompetitiveGradientOptim/blob/main/Not%20MVI.gif)

$f(x, y) = (x − 1/2)(y − 1/2) +\frac{1}{3}e^{−(x − 1/4)^2 − (y − 3/4)^2}$ : Vanishing incoherent region 

![alt-text](https://github.com/AbhijeetiitmVyas/CompetitiveGradientOptim/blob/main/vanishing%20in%20exponential.gif)

