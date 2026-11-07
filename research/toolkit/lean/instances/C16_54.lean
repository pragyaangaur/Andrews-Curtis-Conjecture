import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 54 of the cap-16 certificate: slots 55296 .. 56319 -/
theorem chk_54 : chunkCheck 16 T stdSt 55296 1024 = true := by decide +kernel

end Row16
