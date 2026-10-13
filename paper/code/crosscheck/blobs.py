import sys
from PIL import Image
import numpy as np
from scipy import ndimage
for k in ['Gamma','Delta','Theta','Lambda','Xi','Pi','Sigma','Phi','Psi']:
    a=np.array(Image.open(k+'.png').convert('L'))<60
    # opening with a disc to keep only fat blobs
    r=11
    yy,xx=np.mgrid[-r:r+1,-r:r+1]; disc=(xx*xx+yy*yy)<=r*r
    o=ndimage.binary_opening(a,structure=disc)
    lab,n=ndimage.label(o)
    out=[]
    for i in range(1,n+1):
        ys,xs=np.nonzero(lab==i)
        out.append((round(xs.mean()),round(ys.mean()),len(xs)))
    print(k,a.shape,out)
