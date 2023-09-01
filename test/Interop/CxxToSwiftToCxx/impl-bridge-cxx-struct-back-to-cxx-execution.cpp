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
class TestClass {
public:
    void testMe(int y) const;
    
    int mutateAndReturn(int y);

    int x;
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

#define OSTypeID(type)   (type::metaClass)

#define OSDynamicCast(type, inst)   \
    ((type *) OSMetaClassBase::safeMetaCast((inst), OSTypeID(type)))



struct OSMetaClass;



struct OSMetaClassBase {

    
    static OSMetaClassBase *safeMetaCast(const OSMetaClassBase *inst,
                                         const OSMetaClass *meta);
    static OSMetaClassBase *requiredMetaCast(const OSMetaClassBase *inst,
                                             const OSMetaClass *meta);
    virtual ~OSMetaClassBase();
    virtual void retain() const;
    virtual void release() const;
    

    
} __attribute__((swift_attr("import_reference")))
  __attribute__((swift_attr("import_reference_hierarchy:osDynamicCastForSwift")))
  __attribute__((swift_attr("retain:OSMetaClassBase_retain")))
  __attribute__((swift_attr("release:OSMetaClassBase_release")));

// This function is used to.
template<class T>
static inline T *osDynamicCastForSwift(OSMetaClassBase *inst) {
    return OSDynamicCast(T, inst);
}

inline void OSMetaClassBase_retain(OSMetaClassBase *frt) {
    frt->retain();
}
inline void OSMetaClassBase_release(OSMetaClassBase *frt) {
    frt->release();
}

struct OSObject : public OSMetaClassBase {
    virtual ~OSObject();

    OSObject *getProperty(const char *name);
    
    OSObject *getAnotherFriend(int x);
    
    static const OSMetaClass * const metaClass;
} __attribute__((swift_attr("import_reference")))
__attribute__((swift_attr("import_reference_hierarchy:osDynamicCastForSwift")))
  __attribute__((swift_attr("retain:OSMetaClassBase_retain")))
  __attribute__((swift_attr("release:OSMetaClassBase_release")));

template<class T>
inline T osDynamicCast(const OSObject *value) {
    return ((T) OSMetaClassBase::safeMetaCast(value, OSObject::metaClass)); // FIXME
}


struct OSString: public OSObject {
    virtual ~OSString();

    const char *getStr() {
        return str;
    }
    
    static const OSMetaClass * const metaClass;
private:
    const char *str = "test str";
} __attribute__((swift_attr("import_reference")))
__attribute__((swift_attr("import_reference_hierarchy:osDynamicCastForSwift")))
  __attribute__((swift_attr("retain:OSMetaClassBase_retain")))
  __attribute__((swift_attr("release:OSMetaClassBase_release")));

//--- use-cxx-types.swift
import CxxTest

/*
public func testCast(_ x: OSObject) {
    guard let str = x as? OSString else {
        return
    }
    let value = str.getStr()
}*/

@_cxxImplementation
extension TestClass {
    public func testMe(y: CInt) {
        print("Don't thread on me mr \(x) , \(y)!")
    }
    public mutating func mutateAndReturn(y: CInt) -> CInt {
        x += y
        return x - y
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
int main() {
  TestClass x;
  x.x = 42;
  x.testMe(11);
  assert(x.mutateAndReturn(22) == 42);
  assert(x.x == 64);
    
    SubclassFRT frt;
    frt.doSomething();
  return 0;
}
// CHECK: Don't thread on me mr 42 , 11!
// CHECK: subclass is doing something
