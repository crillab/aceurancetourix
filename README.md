# Aceurancetourix - The JUniverse adapter for ACE.

| License | Linux                                                                                                                                                         & Windows | SonarCloud |
| -------- |--------------------------------------------------------------------------------------------------------------------------------------------------------------- |-------- |
| [![License: GPL v3](https://img.shields.io/badge/License-GPL%20v3-blue.svg)](http://www.gnu.org/licenses/gpl-3.0)     | [![Build Status](https://github.com/crillab/aceurancetourix/actions/workflows/build-jar.yml/badge.svg)](https://github.com/crillab/aceurancetourix/actions/workflows/build-jar.yml) |    |

## Description
 
`Aceurancetourix` is a [JUNIVERSE](https://github.com/crillab/juniverse)
adapter for the constraint solver [ACE](https://github.com/xcsp3team/ace).

An `IUniverseCSPSolver` implemented using ACE may be obtained by using the `AceSolverFactory`
as follows:

```java
var factory = new AceSolverFactory();
var ace = factory.createCspSolver();
```

Note that, for the moment, it is only possible to add constraint before calling one of the
`solve()` methods.
Once one of these methods have been called, adding constraints to the solver may result in
undefined behaviors.

## Build

The latest release is available [here](https://github.com/crillab/aceurancetourix/releases/latest)

`Aceurancetourix` is developed using [JAVA 10](), [Gradle 7.4.2](https://gradle.org/).
Installing Gradle is required if you want to build from source.
To do so, after having installed all the needed tools, you will need to clone
the project:

```bash
git clone https://github.com/crillab/aceurancetourix.git
cd aceurancetourix
gradle aceurancetourix 
```
