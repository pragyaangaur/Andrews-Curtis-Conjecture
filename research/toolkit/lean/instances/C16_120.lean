import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 120 of the cap-16 certificate: slots 122880 .. 123903 -/
theorem chk_120 : chunkCheck 16 T stdSt 122880 1024 = true := by decide +kernel

end Row16
