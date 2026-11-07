import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 45 of the cap-16 certificate: slots 46080 .. 47103 -/
theorem chk_45 : chunkCheck 16 T stdSt 46080 1024 = true := by decide +kernel

end Row16
