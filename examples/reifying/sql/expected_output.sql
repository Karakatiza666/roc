-- migrations
CREATE TABLE IF NOT EXISTS schema_migrations (id TEXT PRIMARY KEY);

-- migration 001_catalog
CREATE TABLE products (
	id BIGINT NOT NULL,
	price NUMERIC(10, 2) NOT NULL,
	title TEXT NOT NULL,
	PRIMARY KEY (id),
	CHECK (price > 0.0)
);
INSERT INTO schema_migrations (id) VALUES ('001_catalog');

-- migration 002_customers_and_orders
CREATE TABLE customers (
	country VARCHAR(2) NOT NULL,
	id BIGINT NOT NULL,
	name TEXT NOT NULL,
	PRIMARY KEY (id)
);
CREATE TABLE orders (
	customer_id BIGINT NOT NULL,
	discount NUMERIC(3, 2) NOT NULL,
	id BIGINT NOT NULL,
	product_id BIGINT NOT NULL,
	quantity BIGINT NOT NULL,
	PRIMARY KEY (id),
	FOREIGN KEY (customer_id) REFERENCES customers,
	FOREIGN KEY (product_id) REFERENCES products,
	CHECK ((quantity > 0) AND ((discount >= 0.0) AND (discount < 1.0)))
);
INSERT INTO schema_migrations (id) VALUES ('002_customers_and_orders');

-- migration 003_customer_email
ALTER TABLE customers ADD COLUMN email TEXT;
INSERT INTO schema_migrations (id) VALUES ('003_customer_email');

-- migration 004_events
CREATE TABLE events (
	at BLOB NOT NULL,
	id BIGINT NOT NULL,
	title TEXT NOT NULL,
	PRIMARY KEY (id)
);
INSERT INTO schema_migrations (id) VALUES ('004_events');

-- seed
INSERT INTO products (id, price, title) VALUES (1, 249.0, 'Espresso machine');
INSERT INTO products (id, price, title) VALUES (2, 18.5, 'Coffee beans, 1kg');
INSERT INTO products (id, price, title) VALUES (3, 12.25, 'Milk jug');
INSERT INTO products (id, price, title) VALUES (4, 50.0, 'Gift card');

-- seed
INSERT INTO customers (country, email, id, name) VALUES ('GB', 'ada@example.com', 1, 'Ada');
INSERT INTO customers (country, email, id, name) VALUES ('US', NULL, 2, 'Grace');
INSERT INTO customers (country, email, id, name) VALUES ('NL', 'ewd@example.com', 3, 'Edsger');
INSERT INTO customers (country, email, id, name) VALUES ('US', 'oneil@example.com', 4, 'O''Neil');

-- seed
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (1, 0.0, 1, 1, 1);
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (1, 0.1, 2, 2, 12);
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (2, 0.0, 3, 2, 3);
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (2, 0.25, 4, 3, 10);
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (3, 0.0, 5, 4, 2);
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (4, 0.15, 6, 2, 20);

-- seed
INSERT INTO events (at, id, title) VALUES (X'7FFFFFFFFFFFFFFFFFFFB16B6EB10000', 1, 'Supplier founded');
INSERT INTO events (at, id, title) VALUES (X'800000000000000017979CFE362A0000', 2, 'Shop opens');
INSERT INTO events (at, id, title) VALUES (X'800000000000000017BB23F0A5EB0000', 3, 'Spring sale');
INSERT INTO events (at, id, title) VALUES (X'800000000000000017DEAAE315AC0001', 4, 'Stocktake');

-- query: premium
SELECT products.price AS price, products.title AS title, products.price * 1.2 AS with_tax
FROM products
WHERE (products.price >= 20.0) AND (products.title <> 'Gift card')
ORDER BY price DESC;

-- query: in_band
SELECT products.price AS price, products.title AS title
FROM products
WHERE (products.price >= 10.0) AND (products.price <= 20.0)
ORDER BY price;

-- query: contacts
SELECT COALESCE(customers.email, '(none)') AS email, customers.name AS name
FROM customers
WHERE customers.country <> 'NL'
ORDER BY name;

-- query: bulk_lines
SELECT customers.name AS customer, products.title AS product, orders.quantity AS quantity, (products.price * CAST(orders.quantity AS NUMERIC)) * (1.0 - orders.discount) AS total
FROM customers
JOIN orders ON orders.customer_id = customers.id
JOIN products ON orders.product_id = products.id
WHERE orders.quantity >= 10
ORDER BY total DESC;
-- roc: [{"customer":"Ada","product":"Coffee beans, 1kg","quantity":12,"total":199.8},{"customer":"Grace","product":"Milk jug","quantity":10,"total":91.875},{"customer":"O'Neil","product":"Coffee beans, 1kg","quantity":20,"total":314.5}]

-- query: revenue_by_country
SELECT customers.country AS country, COUNT(*) AS orders, SUM((products.price * CAST(orders.quantity AS NUMERIC)) * (1.0 - orders.discount)) AS revenue
FROM customers
JOIN orders ON orders.customer_id = customers.id
JOIN products ON orders.product_id = products.id
GROUP BY customers.country
ORDER BY revenue DESC;
-- roc: [{"country":"GB","orders":2,"revenue":448.8},{"country":"US","orders":3,"revenue":461.875},{"country":"NL","orders":1,"revenue":100.0}]

-- query: orders_of_at_least
-- params: [10]
SELECT *
FROM orders
WHERE ?1 <= orders.quantity;
-- roc: [{"customer_id":1,"discount":0.1,"id":2,"product_id":2,"quantity":12},{"customer_id":2,"discount":0.25,"id":4,"product_id":3,"quantity":10},{"customer_id":4,"discount":0.15,"id":6,"product_id":2,"quantity":20}]

-- query: events_before
-- params: [{"blob": "800000000000000017A960776E0A8000"}]
SELECT *
FROM events
WHERE events.at < ?1;
-- roc: [{"at":{"blob":"7FFFFFFFFFFFFFFFFFFFB16B6EB10000"},"id":1,"title":"Supplier founded"},{"at":{"blob":"800000000000000017979CFE362A0000"},"id":2,"title":"Shop opens"}]

-- query: events_after_negative
-- params: [{"blob": "7FFFFFFFFFFFFFFFFFFFA50CEF85C000"}]
SELECT *
FROM events
WHERE events.at > ?1;
-- roc: [{"at":{"blob":"7FFFFFFFFFFFFFFFFFFFB16B6EB10000"},"id":1,"title":"Supplier founded"},{"at":{"blob":"800000000000000017979CFE362A0000"},"id":2,"title":"Shop opens"},{"at":{"blob":"800000000000000017BB23F0A5EB0000"},"id":3,"title":"Spring sale"},{"at":{"blob":"800000000000000017DEAAE315AC0001"},"id":4,"title":"Stocktake"}]

-- query: events_at
-- params: [{"blob": "800000000000000017DEAAE315AC0001"}]
SELECT *
FROM events
WHERE events.at = ?1;
-- roc: [{"at":{"blob":"800000000000000017DEAAE315AC0001"},"id":4,"title":"Stocktake"}]

-- query: events_not_at
-- params: [{"blob": "800000000000000017979CFE362A0000"}]
SELECT *
FROM events
WHERE NOT (events.at = ?1);
-- roc: [{"at":{"blob":"7FFFFFFFFFFFFFFFFFFFB16B6EB10000"},"id":1,"title":"Supplier founded"},{"at":{"blob":"800000000000000017BB23F0A5EB0000"},"id":3,"title":"Spring sale"},{"at":{"blob":"800000000000000017DEAAE315AC0001"},"id":4,"title":"Stocktake"}]

-- query: same_customer_without_email
-- params: ["US", null, 2, "Grace"]
SELECT *
FROM customers
WHERE (customers.country = ?1) AND (customers.email IS ?2) AND (customers.id = ?3) AND (customers.name = ?4);
-- roc: [{"country":"US","id":2,"name":"Grace"}]

-- query: same_customer_with_email
-- params: ["GB", "ada@example.com", 1, "Ada"]
SELECT *
FROM customers
WHERE (customers.country = ?1) AND (customers.email IS ?2) AND (customers.id = ?3) AND (customers.name = ?4);
-- roc: [{"country":"GB","email":"ada@example.com","id":1,"name":"Ada"}]
