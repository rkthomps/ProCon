
test:
	sbt -J-Xmx10G testOnly ContEnumTests 

start:
	sbt -J-Xmx10G -jvm-debug 5005
