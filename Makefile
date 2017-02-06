.PHONY: all

all: MainClass.class

MainClass.class: MainClass.java
	javac -classpath alloy4.2.jar -d . MainClass.java
