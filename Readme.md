
## Readme


Edgencechain is a pocket-sized implementation of Bitcoin. Its goal is to
be a compact, understandable, working incarnation of 
[the Nakamoto consensus algorithm](https://github.com/EdgeIntelligenceChain/Materials2Study/blob/master/%E6%AF%94%E7%89%B9%E5%B8%81%E7%99%BD%E7%9A%AE%E4%B9%A6.pdf) at the
expense of advanced functionality, speed, and any real usefulness.


## Ubuntu下节点启动方式

### 1.python3.6.7的安装
所需python环境 3.6.7， 下载地址 https://www.python.org/ftp/python/3.6.7/Python-3.6.7.tgz 
```
tar -xzf Python-3.6.7.tgz
cd Python-3.6.7
./configure --enable-optimizations  --prefix=/usr/local/python3.7/
#prefix参数配置安装路径
make 
sudo make install
```

### 2.python虚拟环境的启动和配置
在EdgenceChain工程目录下启动python虚拟环境
```
virtualenv --no-site-packages -p /usr/local/python3.6.7/bin/python3.6  venv
source venv/bin/activate
```
安装依赖
```
pip install -r requirements.txt
```

### 3.节点端口设置
1.当前结点端口的设置是在params/Params.py的PORT_CURRENT字段。 举例：将该节点的端口设置为9997： 
*PORT_CURRENT = int(9997)*
2.如果该节点要与已经在运行的节点连接，则必须配置该参数，该参数位于params/Params.py的PEERS字段，节点由一个Tuple类型的(ip,port)表示其ip和port信息。可以配置多个这样的节点。 
*PEERS: Iterable[Tuple] = list([('127.0.0.1', 9997)])*

### 4.节点运行
在EdgenceChain工程目录下
```
python main.py
```
