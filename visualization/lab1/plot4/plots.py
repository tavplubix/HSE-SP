import numpy as np
import matplotlib.pyplot as plt

labels=['Отдельные дома', 'Полуотдельные', 'Таунхаусы', 'Квартиры', 'Другие']

p0 = np.genfromtxt('p0.csv', delimiter=',').T / 1000
p1 = np.genfromtxt('p1.csv', delimiter=',').T / 1000
p2 = np.genfromtxt('p2.csv', delimiter=',').T / 1000
p3 = np.genfromtxt('p3.csv', delimiter=',').T / 1000
p4 = np.genfromtxt('p4.csv', delimiter=',').T / 1000
print(p0.T)
plt.rcParams.update({'font.size': 14})

fig, ax = plt.subplots(figsize=(15, 15))

ybinwidth = 50
ymax = 2000 #np.max(np.concatenate([p0, p1, p2, p3, p4]))
ymin = 100 #np.min(np.concatenate([p0, p1, p2, p3, p4]))
print(ymin, ymax)
ybins = np.arange(ymin, ymax + ybinwidth, ybinwidth)
print(ybins)
ax.hist([p3, p2, p1, p4, p0], bins=ybins, histtype='bar', stacked=True, label=labels)
ax.set(xlabel='Цена (тысячи фунтов, бины по 50 тысяч)', ylabel='Количество сделок', title='Распределения цен на разные типы жилой недвижимости в Лондоне в 2020 году')
ax.legend()	


fig.savefig("types_prices.png")
plt.show()



