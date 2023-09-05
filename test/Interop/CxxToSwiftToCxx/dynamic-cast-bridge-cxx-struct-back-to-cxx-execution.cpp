// RUN: %empty-directory(%t)
// RUN: split-file %s %t

// RN: %target-swift-ide-test -print-module -module-to-print=CxxTest -I %t -source-filename=x -enable-experimental-cxx-interop  | %FileCheck %s

// RUN: %target-swift-frontend -typecheck %t/use-cxx-types.swift -typecheck -module-name UseCxx -emit-clang-header-path %t/UseCxx.h -I %t -enable-experimental-cxx-interop -disable-availability-checking



// RUN: %target-interop-build-clangxx -std=c++20 -c %t/use-swift-cxx-types.cpp -I %t -o %t/swift-cxx-execution.o -g
// RUN: %target-interop-build-clangxx -std=c++20 -c %t/impl.cpp -I %t -o %t/impl.o

// RUN: %target-interop-build-swift %t/use-cxx-types.swift -o %t/swift-cxx-execution -Xlinker %t/swift-cxx-execution.o -Xlinker %t/impl.o -module-name UseCxx -Xfrontend -entry-point-function-name -Xfrontend swiftMain -I %t -g -Xfrontend -disable-availability-checking

// RUN: %target-codesign %t/swift-cxx-execution
// RUN: %target-run %t/swift-cxx-execution | %FileCheck %s

// REQUIRES: executable_test

//--- module.modulemap
module CxxTest {
    header "header.h"
    requires cplusplus
}

//--- impl.cpp

#include "header.h"

OSMetaClassBase::~OSMetaClassBase() {}

void OSMetaClassBase::retain() {}
void OSMetaClassBase::release() {}

OSMetaClassBase *OSMetaClassBase::safeMetaCast(const OSMetaClassBase *inst,
                                            const OSMetaClass *meta) {
    if (inst->getMetaClass() == meta) {
        return const_cast<OSMetaClassBase *>(inst);
    }
    return nullptr;
}

OSObject::~OSObject() {}

OSObject *OSObject::getProperty(const char *name) {
    return nullptr;
}

void OSObject::retain() {
    ++retainCount;
}
void OSObject::release() {
    --retainCount;
    if (retainCount == 0) {
        delete this;
    }
}

struct OSMetaClass { int n; };

OSMetaClass OSObjectMeta;

const OSMetaClass * const OSObject::metaClass = &OSObjectMeta;

const OSMetaClass *OSObject::getMetaClass() const {
    return OSObject::metaClass;
}

OSString::~OSString() {}

OSMetaClass OSStringMeta;

const OSMetaClass * const OSString::metaClass = &OSStringMeta;

const OSMetaClass *OSString::getMetaClass() const {
    return OSString::metaClass;
}

//--- header.h

#define OSTypeID(type)   (type::metaClass)

#define OSDynamicCast(type, inst)   \
    ((type *) OSMetaClassBase::safeMetaCast((inst), OSTypeID(type)))

struct OSMetaClass;

#define SHARED_OS_OBJECT \
__attribute__((swift_attr("import_reference"))) \
  __attribute__((swift_attr("import_reference_hierarchy:osDynamicCastForSwift"))) \
  __attribute__((swift_attr("retain:OSMetaClassBase_retain"))) \
  __attribute__((swift_attr("release:OSMetaClassBase_release")))

struct OSMetaClassBase {
    static OSMetaClassBase *safeMetaCast(const OSMetaClassBase *inst,
                                         const OSMetaClass *meta);
    static OSMetaClassBase *requiredMetaCast(const OSMetaClassBase *inst,
                                             const OSMetaClass *meta);
    virtual ~OSMetaClassBase();
    virtual void retain();
    virtual void release();
    virtual const OSMetaClass *getMetaClass() const = 0;
} SHARED_OS_OBJECT;

// This function is used to perform the dynamic casting on the Swift side.
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

    virtual void retain() override;
    virtual void release() override;
    
    const OSMetaClass *getMetaClass() const override;
    static const OSMetaClass * const metaClass;
private:
    int retainCount = 1;
} SHARED_OS_OBJECT;

struct OSString: public OSObject {
    OSString(const char *str) : str(str) {}
    virtual ~OSString();

    const char *getStr() {
        return str;
    }

    const OSMetaClass *getMetaClass() const override;
    static const OSMetaClass * const metaClass;
private:
    const char *str = str;
} SHARED_OS_OBJECT;












// My Custom Driver implemented in Swift.

struct OSCustomDriver: public OSObject {
    virtual ~OSCustomDriver() {}
    
    // Implemented in Swift.
    virtual void run(OSObject *input);

    // Additional boilerplate for IOKit...
} SHARED_OS_OBJECT;

//--- use-cxx-types.swift
import CxxTest

@_cxxImplementation
extension OSCustomDriver {
    public func run(input: OSObject) {
        print("running the driver!")
        // Downcasting using an imported Swift class hierarchy
        if let str = input as? OSString {
            print("🤖 driver received string '\(String(cString: str.getStr()!))'!")

            // Oh and by the way, we can now upcast too
            let base: OSObject = str
        } else {
            print("😪 driver received unknown input")
        }
        
    }
}

//--- use-swift-cxx-types.cpp
#include "header.h"
#include <assert.h>
int main() {
  auto driver = new OSCustomDriver;
  auto string = new OSString("Hey Swift driver");
  driver->run(string);
  driver->run(driver);
  return 0;
}
