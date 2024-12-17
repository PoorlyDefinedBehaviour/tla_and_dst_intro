### ABout

The code in Go is broken.

### Start MySQL

docker run --name mysql -e MYSQL_ROOT_PASSWORD=password -p 3306:3306 -d mysql

docker exec -it mysql mysql -uroot -ppassword

create database dev;

use dev;

create table balances (
  id VARCHAR(255) NOT NULL,
  balance int NOT NULL,
  PRIMARY KEY(id)
);

insert into balances (id, balance)
values ("alice", 0), ("bob", 0);

### Send requests

curl localhost:9001/deposit -d '{"from": "alice", "amount": 1}'
curl localhost:9001/transfer -d '{"from": "alice", "to": "bob", "amount": 1}'
curl localhost:9001/withdraw -d '{"from": "bob", "amount": 1}'