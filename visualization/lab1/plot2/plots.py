import numpy as np
import matplotlib.pyplot as plt


data = np.genfromtxt('ypls.csv', delimiter=',')
print(data[0])
#x = np.random.randn(1000)
#y = np.random.randn(1000)
y = data.T[1] / 1000 # price
x = data.T[0]		 # year 

print(x)
print(y)

def scatter_hist(x, y, ax, ax_histx, ax_histy):
    # no labels
    ax_histx.tick_params(axis="x", labelbottom=False)
    ax_histy.tick_params(axis="y", labelleft=False)

    # the scatter plot:
    ax.scatter(x, y, s=1)

    # now determine nice limits by hand:
    xbinwidth = 1
    xmax = np.max(x)
    xmin = np.min(x)
    xbins = np.arange(xmin, xmax + xbinwidth, xbinwidth)
    ax_histx.hist(x, bins=xbins, weights=[50,]*len(x))

    ybinwidth = 50
    ymax = np.max(y)
    ymin = np.min(y)
    ybins = np.arange(ymin, ymax + ybinwidth, ybinwidth)
    ax_histy.hist(y, bins=ybins, orientation='horizontal', weights=[50,]*len(x))


left, width = 0.1, 0.65
bottom, height = 0.1, 0.65
spacing = 0.005


rect_scatter = [left, bottom, width, height]
rect_histx = [left, bottom + height + spacing, width, 0.2]
rect_histy = [left + width + spacing, bottom, 0.2, height]

# start with a square Figure
fig = plt.figure(figsize=(16, 12))

ax = fig.add_axes(rect_scatter)
ax_histx = fig.add_axes(rect_histx, sharex=ax)
ax_histy = fig.add_axes(rect_histy, sharey=ax)

# use the previously defined function
scatter_hist(x, y, ax, ax_histx, ax_histy)


fig.suptitle('Разброс цен на жилую недвижимость в Лондоне', fontsize=15)
ax.set(xlabel='Год', ylabel='Цена (тысячи фунтов)')
ax_histx.set(ylabel='Кол-во сделок (бины по 1 году)')
ax_histy.set(xlabel='Кол-во сделок (бины по 50 тысяч фунтов)')
ax.grid()
#ax.legend()


fig.savefig("years_and_prices.png")
plt.show()



