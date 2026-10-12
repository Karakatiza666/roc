-- migrations
CREATE TABLE IF NOT EXISTS schema_migrations (id TEXT PRIMARY KEY);

-- migration 001_catalog
CREATE TABLE products (
	id BIGINT NOT NULL,
	title TEXT NOT NULL,
	price NUMERIC(10, 2) NOT NULL,
	PRIMARY KEY (id),
	CHECK (price > 0.0)
);
INSERT INTO schema_migrations (id) VALUES ('001_catalog');

-- migration 002_customers_and_orders
CREATE TABLE customers (
	id BIGINT NOT NULL,
	name TEXT NOT NULL,
	country VARCHAR(2) NOT NULL,
	PRIMARY KEY (id)
);
CREATE TABLE orders (
	id BIGINT NOT NULL,
	customer_id BIGINT NOT NULL,
	product_id BIGINT NOT NULL,
	quantity BIGINT NOT NULL,
	discount NUMERIC(3, 2) NOT NULL,
	PRIMARY KEY (id),
	FOREIGN KEY (customer_id) REFERENCES customers,
	FOREIGN KEY (product_id) REFERENCES products,
	CHECK ((quantity > 0) AND ((discount >= 0.0) AND (discount < 1.0)))
);
INSERT INTO schema_migrations (id) VALUES ('002_customers_and_orders');

-- migration 003_customer_email
ALTER TABLE customers ADD COLUMN email TEXT;
INSERT INTO schema_migrations (id) VALUES ('003_customer_email');

-- seed
INSERT INTO products (id, price, title) VALUES (1, 249.0, 'Espresso machine');
INSERT INTO products (id, price, title) VALUES (2, 18.5, 'Coffee beans, 1kg');
INSERT INTO products (id, price, title) VALUES (3, 12.25, 'Milk jug');
INSERT INTO products (id, price, title) VALUES (4, 50.0, 'Gift card');

-- seed
INSERT INTO customers (country, email, id, name) VALUES ('GB', 'ada@example.com', 1, 'Ada');
INSERT INTO customers (country, id, name) VALUES ('US', 2, 'Grace');
INSERT INTO customers (country, email, id, name) VALUES ('NL', 'ewd@example.com', 3, 'Edsger');
INSERT INTO customers (country, email, id, name) VALUES ('US', 'oneil@example.com', 4, 'O''Neil');

-- seed
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (1, 0.0, 1, 1, 1);
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (1, 0.1, 2, 2, 12);
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (2, 0.0, 3, 2, 3);
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (2, 0.25, 4, 3, 10);
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (3, 0.0, 5, 4, 2);
INSERT INTO orders (customer_id, discount, id, product_id, quantity) VALUES (4, 0.15, 6, 2, 20);

-- query: premium
SELECT products.title AS title, products.price AS price, products.price * 1.2 AS with_tax
FROM products
WHERE (products.price >= 20.0) AND (products.title <> 'Gift card')
ORDER BY price DESC;

-- query: in_band
SELECT products.title AS title, products.price AS price
FROM products
WHERE (products.price >= 10.0) AND (products.price <= 20.0)
ORDER BY price;

-- query: contacts
SELECT customers.name AS name, COALESCE(customers.email, '(none)') AS email
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
