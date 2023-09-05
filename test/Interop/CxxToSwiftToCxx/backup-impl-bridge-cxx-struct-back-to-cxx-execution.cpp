// RUN: %empty-directory(%t)
// RUN: split-file %s %t

// RN: %target-swift-ide-test -print-module -module-to-print=CxxTest -I %t -source-filename=x -enable-experimental-cxx-interop  | %FileCheck %s

// RUN: %target-swift-frontend -typecheck %t/use-cxx-types.swift -typecheck -module-name UseCxx -emit-clang-header-path %t/UseCxx.h -I %t -enable-experimental-cxx-interop -disable-availability-checking



// RUN: %target-interop-build-clangxx -std=c++20 -c %t/use-swift-cxx-types.cpp -I %t -o %t/swift-cxx-execution.o -g
// RUN: %target-interop-build-swift %t/use-cxx-types.swift -o %t/swift-cxx-execution -Xlinker %t/swift-cxx-execution.o -module-name UseCxx -Xfrontend -entry-point-function-name -Xfrontend swiftMain -I %t -g -Xfrontend -disable-availability-checking

// RUN: %target-codesign %t/swift-cxx-execution
// RUN: %target-run %t/swift-cxx-execution | %FileCheck %s

// REQUIRES: executable_test

//--- module.modulemap
module CxxTest {
    header "header.h"
    requires cplusplus
}

//--- header.h
#pragma once

#include <string>

class WebBrowserResourceLoader {
public:
    int loadResource(const std::string &x);
    
    bool isLoaded(int resourceID) const;

// Note: fields are public:
    int resourceCounter = 0;
    void *resources = nullptr;
};

class TestFRT {
public:
    virtual ~TestFRT() {}
    
    virtual void doSomething() = 0;

    int referenceCounter = 1;
} __attribute__((swift_attr("import_reference")))
  __attribute__((swift_attr("retain:testFRTRetain")))
  __attribute__((swift_attr("release:testFRTRelease")))
  ;

inline void testFRTRetain(TestFRT *frt) {
    frt->referenceCounter++;
}
inline void testFRTRelease(TestFRT *frt) {
    frt->referenceCounter--;
    if (frt->referenceCounter == 0) {
        delete frt;
    }
}

class SubclassFRT: TestFRT {
public:
    void doSomething() override; // FIXME: const problem
} __attribute__((swift_attr("import_reference")))
  __attribute__((swift_attr("retain:testFRTRetain")))
  __attribute__((swift_attr("release:testFRTRelease")));


//--- use-cxx-types.swift
import CxxTest
import CxxStdlib

@_cxxImplementation
extension WebBrowserResourceLoader {
    public mutating func loadResource(name: std.string) -> CInt {
        print("Loading resource \(name)...")
        resourceCounter += 1
        return resourceCounter
    }

    public func isLoaded(resourceID: CInt) -> Bool {
        resourceID <= resourceCounter
    }
}

@_cxxImplementation
extension SubclassFRT {
    public func doSomething() {
        print("subclass is doing something")
    }
}



//--- use-swift-cxx-types.cpp
#include "header.h"
#include <assert.h>
#include <string>
int main() {
  WebBrowserResourceLoader loader;
  int id = loader.loadResource("hello.world.avi");
  assert(loader.isLoaded(id));

    
    SubclassFRT frt;
    frt.doSomething();
  return 0;
}
// CHECK: Don't thread on me mr 42 , 11!
// CHECK: subclass is doing something
