import numpy as np
import matplotlib.pyplot as plt


#labels=['Detached', 'Semi-Detached', 'Terraced', 'Flats', 'Other']
labels=['Отдельные дома', 'Полуотдельные', 'Таунхаусы', 'Квартиры', 'Другие']
types = np.genfromtxt('types.csv', delimiter=',')
types_l = np.genfromtxt('types_l.csv', delimiter=',')
types_m = np.genfromtxt('types_m.csv', delimiter=',')
types_b = np.genfromtxt('types_b.csv', delimiter=',')
print(types.T)
print(types_l.T)
print(types_m.T)
print(types_b.T)

plt.rcParams.update({'font.size': 14})


fig, axs = plt.subplots(2, 2, figsize=(16,14))

wedges, texts, autotexts = axs[0, 0].pie(types.T, autopct='%.0f%%', pctdistance=0.8, counterclock=False, startangle=180, radius=1.4, wedgeprops=dict(width=0.5, edgecolor='w'), textprops=dict(color="w"))
axs[0,0].legend(wedges, labels, title="Типы", loc=(-0.47, 0.85))
plt.setp(autotexts, size=12, weight="bold")
axs[0,0].text(0, 0, 'Все города', horizontalalignment='center', verticalalignment='center', fontdict={'fontsize': 20})
#axs[0,0].set_title("Все города", fontdict={'fontsize': 12}, loc='center')

wedges, texts, autotexts = axs[0, 1].pie(types_l.T, autopct='%.0f%%', pctdistance=0.8, counterclock=False, startangle=180, radius=1.4, wedgeprops=dict(width=0.5, edgecolor='w'), textprops=dict(color="w"))
plt.setp(autotexts, size=12, weight="bold")
#axs[0,1].set_title("Лондон")
axs[0,1].text(0, 0, 'Лондон', horizontalalignment='center', verticalalignment='center', fontdict={'fontsize': 20})

wedges, texts, autotexts = axs[1, 0].pie(types_m.T, autopct='%.0f%%', pctdistance=0.8, counterclock=False, startangle=180, radius=1.4, wedgeprops=dict(width=0.5, edgecolor='w'), textprops=dict(color="w"))
plt.setp(autotexts, size=12, weight="bold")
#axs[1,0].set_title("Манчестер")
axs[1,0].text(0, 0, 'Манчестер', horizontalalignment='center', verticalalignment='center', fontdict={'fontsize': 20})

wedges, texts, autotexts = axs[1, 1].pie(types_b.T, autopct='%.0f%%', pctdistance=0.8, counterclock=False, startangle=180, radius=1.4, wedgeprops=dict(width=0.5, edgecolor='w'), textprops=dict(color="w"))
plt.setp(autotexts, size=12, weight="bold")
#axs[1,1].set_title("Бристоль")
axs[1,1].text(0, 0, 'Бристоль', horizontalalignment='center', verticalalignment='center', fontdict={'fontsize': 20})


fig.suptitle('Типы жилой недвижимости на рынке Великобритании', fontsize=24)
#ax.legend()

fig.savefig("types.png")
plt.show()



