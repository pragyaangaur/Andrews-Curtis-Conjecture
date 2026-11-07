import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 201 of the cap-16 certificate: slots 205824 .. 206847 -/
theorem chk_201 : chunkCheck 16 T stdSt 205824 1024 = true := by decide +kernel

end Row16
