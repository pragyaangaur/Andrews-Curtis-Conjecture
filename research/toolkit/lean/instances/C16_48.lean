import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 48 of the cap-16 certificate: slots 49152 .. 50175 -/
theorem chk_48 : chunkCheck 16 T stdSt 49152 1024 = true := by decide +kernel

end Row16
