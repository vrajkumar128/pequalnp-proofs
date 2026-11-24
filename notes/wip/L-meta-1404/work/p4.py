from depthsat import *
print('P4oMAJ'); mindepth(12,lambda z:(maj(*z[0:3]) and maj(*z[3:6])) or (maj(*z[3:6]) and maj(*z[6:9])) or (maj(*z[6:9]) and maj(*z[9:12])))
