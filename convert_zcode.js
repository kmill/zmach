var fs = require('fs');

function convert(filename) {
  fs.readFile(filename, function (err, data) {
    if (err) throw err;
    var b64 = data.toString('base64');
    var code = "loadData('base64', " + JSON.stringify(b64) + ");";
    fs.writeFile(filename + ".js", code, function (err) {
      if (err) throw err;
    });
  });
}
//fs.read

convert(process.argv[2]);
