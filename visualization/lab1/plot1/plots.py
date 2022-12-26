import numpy as np
import matplotlib.pyplot as plt


year_to_price_london = np.genfromtxt('year_price_l.csv', delimiter=',')
year_to_price_manchester = np.genfromtxt('year_price_m.csv', delimiter=',')
year_to_price_bristol = np.genfromtxt('year_price_b.csv', delimiter=',')
year_to_price_birm = np.genfromtxt('year_price_bi.csv', delimiter=',')
year_to_price_not = np.genfromtxt('year_price_no.csv', delimiter=',')

plt.rcParams.update({'font.size': 14})

print(year_to_price_london.T[1])
print(year_to_price_manchester.T[1])
print(year_to_price_bristol.T[1])

fig, ax = plt.subplots(figsize=(16,12))
plt.yticks(range(0, 1100, 100))
ax.plot(year_to_price_london.T[0], year_to_price_london.T[1] / 1000, label="Лондон")
ax.plot(year_to_price_bristol.T[0], year_to_price_bristol.T[1] / 1000, label="Бристоль")
ax.plot(year_to_price_manchester.T[0], year_to_price_manchester.T[1] / 1000, label="Манчетсер")
ax.plot(year_to_price_birm.T[0], year_to_price_birm.T[1] / 1000, label="Бирмингем")
ax.plot(year_to_price_not.T[0], year_to_price_not.T[1] / 1000, label="Ноттингем")

ax.set(xlabel='Год', ylabel='Средняя цена, тысячи фунтов', title='Цены на жилую недвижимость в городах Великобритании')
ax.legend()
ax.grid()

fig.savefig("year_to_price.png")
plt.show()



