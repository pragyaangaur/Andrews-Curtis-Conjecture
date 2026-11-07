import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 39 of the cap-16 certificate: slots 39936 .. 40959 -/
theorem chk_39 : chunkCheck 16 T stdSt 39936 1024 = true := by decide +kernel

end Row16
