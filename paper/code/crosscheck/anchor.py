from PIL import Image
import numpy as np, json
from scipy.signal import fftconvolve
from scipy import ndimage
T=(np.array(Image.open('Delta.png').convert('L'))[360:415,225:275]<80).astype(float)
T-=T.mean()
res={}
for k in ['Gamma','Delta','Theta','Lambda','Xi','Pi','Sigma','Phi','Psi']:
    a=(np.array(Image.open(k+'.png').convert('L'))<80).astype(float)
    c=fftconvolve(a,T[::-1,::-1],mode='same')
    y,x=np.unravel_index(np.argmax(c),c.shape)
    # Delta reference: glyph patch centre (250,387.5) <-> hex centre (250,388)
    res[k]=(int(x),int(y))
print(res)
json.dump(res,open('../gamma_centres.json','w'))
