VeyMont ![master status](https://img.shields.io/travis/utwente-fmt/vercors/master?label=master) ![dev status](https://img.shields.io/travis/utwente-fmt/vercors/dev?label=dev)
=======

This Git banch of VerCors hosts VeyMont, a tool for verification of concurrent message passing programs. VeyMont has been build on top of VerCors.

## Installation: Building from source code
When building VerCors and VeyMont, you additionally need these dependencies:

- A Java _Development_ Kit, version 11 or greater, either OpenJDK or Oracle.
- Git (on Windows you need Git Bash, see <https://git-scm.com/downloads>)
- Scala SBT, version 1.3.0 or greater (see <http://www.scala-sbt.org> for instructions)

1. Clone this Git branch using `git clone https://github.com/utwente-fmt/vercors.git`, move into the cloned directory, `cd vercors`, and switch to the VeyMont branch using `git checkout session-generation`.
2. Run `sbt compile` to compile VerCors.
3. Test whether the build was successful by running `./bin/vct --test=examples/manual --tool=silicon --lang=pvl,java --progress`.

The last command tests the VerCors installation by verifying a large collection of examples (from the `./examples` directory). This command should eventually report that `all ? tests passed`. There are also intstructions for importing VerCors into either eclipse or IntelliJ IDEA [here](https://github.com/utwente-fmt/vercors/wiki).


## Running VerCors and VeyMont
The VerCors tool can be used by running:

 `./bin/vct --silicon <filepath>`, with `<filepath>` the path of the (Java, C, or PVL) file to verify.

The VeyMont tool can be used by running:

 `./bin/vct --veymont <filepath-to-output-file-for-local-programs> <filepath-to-global-program>`

VerCors verifies programs that are annotated with JML-style specifications (the underlying theory uses separation logic with permission accounting). Details on the specification language can be found on the VerCors [Wiki pages](https://github.com/utwente-fmt/vercors/wiki). Furthermore, a large collection of example programs can be found (and verified) in the `/examples` directory. In particular, example global programs for VeyMont can be found in `examples/veymont-global-programs`.

## Source code
All VeyMont specific source code can be found in the directory `src/main/java/vct/col/veymont`
The global programs of our case studies can be found in the directory `examples/verymont-global-programs`

## License
Copyright (c) 2008 - 2019 Formal Methods and Tools, University of Twente
All rights reserved.

The license to VerCors is a mozilla open source license as described in LICENSE.TXT in the root of this project. It is a free to use, share-alike license. Should this license be too restrictive for your purpose, please let us know by creating an issue in our bug tracker. Direct contributors (people who send us pull-requests or edit this repository directly) are expected to agree with any license that the University of Twente might decide. If you do not agree with future license changes, please instead fork this repository as allowed under the conditions of LICENSE.TXT.
