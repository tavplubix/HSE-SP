
-- wget http://prod.publicdata.landregistry.gov.uk.s3-website-eu-west-1.amazonaws.com/pp-complete.csv


CREATE TABLE uk_price_paid
(
    price UInt32,
    date Date,
    postcode1 LowCardinality(String),
    postcode2 LowCardinality(String),
    type Enum8('terraced' = 1, 'semi-detached' = 2, 'detached' = 3, 'flat' = 4, 'other' = 0),
    is_new UInt8,
    duration Enum8('freehold' = 1, 'leasehold' = 2, 'unknown' = 0),
    addr1 String,
    addr2 String,
    street LowCardinality(String),
    locality LowCardinality(String),
    town LowCardinality(String),
    district LowCardinality(String),
    county LowCardinality(String),
    category UInt8
) ENGINE = MergeTree ORDER BY (postcode1, postcode2, addr1, addr2);


-- plot 1
SELECT toYear(date) AS year, round(avg(price)) AS price  FROM uk_price_paid WHERE town='LONDON' GROUP BY year ORDER BY year FORMAT CSV;
SELECT toYear(date) AS year, round(avg(price)) AS price  FROM uk_price_paid WHERE town='MANCHESTER' GROUP BY year ORDER BY year FORMAT CSV;
SELECT toYear(date) AS year, round(avg(price)) AS price  FROM uk_price_paid WHERE town='BRISTOL' GROUP BY year ORDER BY year FORMAT CSV;
SELECT toYear(date) AS year, round(avg(price)) AS price  FROM uk_price_paid WHERE town='BIRMINGHAM' GROUP BY year ORDER BY year FORMAT CSV;
SELECT toYear(date) AS year, round(avg(price)) AS price  FROM uk_price_paid WHERE town='NOTTINGHAM' GROUP BY year ORDER BY year FORMAT CSV;


-- plot 2
select count() as c from uk_price_paid group by type order by [5, 3, 2, 1, 4][toInt8(type) + 1] format CSV;
select count() as c from uk_price_paid WHERE town='LONDON' group by type order by [5, 3, 2, 1, 4][toInt8(type) + 1] format CSV;
select count() as c from uk_price_paid WHERE town='MANCHESTER' group by type order by [5, 3, 2, 1, 4][toInt8(type) + 1] format CSV;
select count() as c from uk_price_paid WHERE town='BRISTOL' group by type order by [5, 3, 2, 1, 4][toInt8(type) + 1] format CSV;


-- plot 3
with (select quantile(0.02)(price) from uk_price_paid WHERE town='LONDON') as min, (select quantile(0.98)(price) from uk_price_paid WHERE town='LONDON') as max select toYear(date) + (date - toStartOfYear(date)) / 365, price from uk_price_paid WHERE town='LONDON' and min < price and price < max format CSV;
with (select quantile(0.02)(price) from uk_price_paid WHERE town='LONDON') as min, (select quantile(0.98)(price) from uk_price_paid WHERE town='LONDON') as max select toYear(date), price from uk_price_paid WHERE town='LONDON' and min < price and price < max and sipHash64(date, price, addr1, addr2) % 10 = 0 format CSV;
with (select quantile(0.02)(price) from uk_price_paid WHERE town='LONDON') as min, (select quantile(0.98)(price) from uk_price_paid WHERE town='LONDON') as max select toYear(date) + (date - toStartOfYear(date)) / 365, price from uk_price_paid WHERE town='LONDON' and min < price and price < max and sipHash64(date, price, addr1, addr2) % 100 = 0 format CSV;
with (select quantile(0.02)(price) from uk_price_paid WHERE town='LONDON') as min, (select quantile(0.98)(price) from uk_price_paid WHERE town='LONDON') as max select toYear(date), price from uk_price_paid WHERE town='LONDON' and min < price and price < max and sipHash64(date, price, addr1, addr2) % 1000 = 0 format CSV;

WITH
    (
        SELECT min(toYear(date))
        FROM uk_price_paid
    ) AS miny,
    (
        SELECT groupArray(q)
        FROM
        (
            SELECT
                toYear(date) AS d,
                quantile(0.05)(price) AS q
            FROM uk_price_paid
            WHERE town = 'LONDON'
            GROUP BY d
            ORDER BY d ASC
        )
    ) AS min,
    (
        SELECT groupArray(q)
        FROM
        (
            SELECT
                toYear(date) AS d,
                quantile(0.90)(price) AS q
            FROM uk_price_paid
            WHERE town = 'LONDON'
            GROUP BY d
            ORDER BY d ASC
        )
    ) AS max
SELECT
    toYear(date) + ((date - toStartOfYear(date)) / 365),
    price
FROM uk_price_paid
WHERE (town = 'LONDON') AND ((min[(toYear(date) - miny) + 1]) < price) AND (price < max[(toYear(date) - miny) + 1]) AND sipHash64(date, price, addr1, addr2) % 100 = 0
FORMAT CSV




-- plot 4
select price from uk_price_paid WHERE town='LONDON' and toYear(date)=2020 and type=0 format CSV;
select price from uk_price_paid WHERE town='LONDON' and toYear(date)=2020 and type=1 format CSV;
select price from uk_price_paid WHERE town='LONDON' and toYear(date)=2020 and type=2 format CSV;
select price from uk_price_paid WHERE town='LONDON' and toYear(date)=2020 and type=3 format CSV;
select price from uk_price_paid WHERE town='LONDON' and toYear(date)=2020 and type=4 format CSV;


