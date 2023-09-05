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
    int loadResource(const std::string &name);
    
    bool isLoaded(int resourceID) const;

    int resourceCounter = 0; // Note: field must be public for now.
};

//--- use-cxx-types.swift
import CxxTest
import CxxStdlib

@_cxxImplementation
extension WebBrowserResourceLoader {
    public mutating func loadResource(name: std.string) -> CInt {
        print("Loading resource \(name)...")
        resourceCounter += 1
        // Call into Swift macOS SDK APIs here :)
        return resourceCounter
    }

    public func isLoaded(resourceID: CInt) -> Bool {
        resourceID <= resourceCounter
    }
}

//--- use-swift-cxx-types.cpp
#include "header.h"
#include <assert.h>

int main() {
  WebBrowserResourceLoader loader;
  int id = loader.loadResource("hello.world.avi");
  assert(loader.isLoaded(id));
  return 0;
}

// CHECK: Loading resource hello.world.avi...
