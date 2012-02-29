var URL = require('url'),
    util = require('util'),
    jsmin = require('./jsmin'),
    events = require('events'),
    Buffer = require('buffer').Buffer,
    fs = require('fs'),
    path = require('path'),
    jsdom = require('jsdom'),
    uglifyjs = require('uglify-js'),
    jsp = uglifyjs.parser,
    pro = uglifyjs.uglify,
    compress = null, // import only when required - might make the command line tool easier to use
    http = {
      http: require('http'),
      https: require('https')
    };


// Options for converting relative to absolute
// TODO: Make this something you can pass in from the bin
var rootUrl = 'http://app.dsharpdiabetes.com/sessions/new';
var host = 'app.dsharpdiabetes.com';
var base_url = '/';
var protocol = 'http:';

var rel_to_abs = function(url){
    /* Only accept commonly trusted protocols:
     * Only data-image URLs are accepted, Exotic flavours (escaped slash,
     * html-entitied characters) are not supported to keep the function fast */
  if(/^(https?|file|ftps?|mailto|javascript|data:image\/[^;]{2,9};):/i.test(url))
         return url; //Url is already absolute

    // base_url was here
    if(url.substring(0,2) == "//")
        return protocol + url;
    else if(url.charAt(0) == "/")
        return protocol + "//" + host + url;
    else if(url.substring(0,2) == "./")
        url = "." + url;
    else if(/^\s*$/.test(url))
        return ""; //Empty = Return nothing
    else url = "../" + url;

    url = base_url + url;
    var i=0
    while(/\/\.\.\//.test(url = url.replace(/[^\/]+\/+\.\.\//g,"")));

    /* Escape certain characters to prevent XSS */
    url = url.replace(/\.$/,"").replace(/\/\./g,"").replace(/"/g,"%22")
            .replace(/'/g,"%27").replace(/</g,"%3C").replace(/>/g,"%3E");
    return url;
};

var replace_all_rel_by_abs = function(html){
    /*HTML/XML Attribute may not be prefixed by these characters (common 
       attribute chars.  This list is not complete, but will be sufficient
       for this function (see http://www.w3.org/TR/REC-xml/#NT-NameChar). */
    var att = "[^-a-z0-9:._]";

    var entityEnd = "(?:;|(?!\\d))";
    var ents = {" ":"(?:\\s|&nbsp;?|&#0*32"+entityEnd+"|&#x0*20"+entityEnd+")",
                "(":"(?:\\(|&#0*40"+entityEnd+"|&#x0*28"+entityEnd+")",
                ")":"(?:\\)|&#0*41"+entityEnd+"|&#x0*29"+entityEnd+")",
                ".":"(?:\\.|&#0*46"+entityEnd+"|&#x0*2e"+entityEnd+")"};
                /* Placeholders to filter obfuscations */
    var charMap = {};
    var s = ents[" "]+"*"; //Short-hand for common use
    var any = "(?:[^>\"']*(?:\"[^\"]*\"|'[^']*'))*?[^>]*";
    /* ^ Important: Must be pre- and postfixed by < and >.
     *   This RE should match anything within a tag!  */

    /*
      @name ae
      @description  Converts a given string in a sequence of the original
                      input and the HTML entity
      @param String string  String to convert
      */
    function ae(string){
        var all_chars_lowercase = string.toLowerCase();
        if(ents[string]) return ents[string];
        var all_chars_uppercase = string.toUpperCase();
        var RE_res = "";
        for(var i=0; i<string.length; i++){
            var char_lowercase = all_chars_lowercase.charAt(i);
            if(charMap[char_lowercase]){
                RE_res += charMap[char_lowercase];
                continue;
            }
            var char_uppercase = all_chars_uppercase.charAt(i);
            var RE_sub = [char_lowercase];
            RE_sub.push("&#0*" + char_lowercase.charCodeAt(0) + entityEnd);
            RE_sub.push("&#x0*" + char_lowercase.charCodeAt(0).toString(16) + entityEnd);
            if(char_lowercase != char_uppercase){
                /* Note: RE ignorecase flag has already been activated */
                RE_sub.push("&#0*" + char_uppercase.charCodeAt(0) + entityEnd);   
                RE_sub.push("&#x0*" + char_uppercase.charCodeAt(0).toString(16) + entityEnd);
            }
            RE_sub = "(?:" + RE_sub.join("|") + ")";
            RE_res += (charMap[char_lowercase] = RE_sub);
        }
        return(ents[string] = RE_res);
    }

    /*
      @name by
      @description  2nd argument for replace().
      */
    function by(match, group1, group2, group3){
        /* Note that this function can also be used to remove links:
         * return group1 + "javascript://" + group3; */
        return group1 + rel_to_abs(group2) + group3;
    }
    /*
      @name by2
      @description  2nd argument for replace(). Parses relevant HTML entities
      */
    var slashRE = new RegExp(ae("/"), 'g');
    var dotRE = new RegExp(ae("."), 'g');
    function by2(match, group1, group2, group3){
        /*Note that this function can also be used to remove links:
         * return group1 + "javascript://" + group3; */
        group2 = group2.replace(slashRE, "/").replace(dotRE, ".");
        return group1 + rel_to_abs(group2) + group3;
    }
    /*
      @name cr
      @description            Selects a HTML element and performs a
                                search-and-replace on attributes
      @param String selector  HTML substring to match
      @param String attribute RegExp-escaped; HTML element attribute to match
      @param String marker    Optional RegExp-escaped; marks the prefix
      @param String delimiter Optional RegExp escaped; non-quote delimiters
      @param String end       Optional RegExp-escaped; forces the match to end
                              before an occurence of <end>
     */
    function cr(selector, attribute, marker, delimiter, end){
        if(typeof selector == "string") selector = new RegExp(selector, "gi");
        attribute = att + attribute;
        marker = typeof marker == "string" ? marker : "\\s*=\\s*";
        delimiter = typeof delimiter == "string" ? delimiter : "";
        end = typeof end == "string" ? "?)("+end : ")(";
        var re1 = new RegExp('('+attribute+marker+'")([^"'+delimiter+']+'+end+')', 'gi');
        var re2 = new RegExp("("+attribute+marker+"')([^'"+delimiter+"]+"+end+")", 'gi');
        var re3 = new RegExp('('+attribute+marker+')([^"\'][^\\s>'+delimiter+']*'+end+')', 'gi');
        html = html.replace(selector, function(match){
            return match.replace(re1, by).replace(re2, by).replace(re3, by);
        });
    }
    /* 
      @name cri
      @description            Selects an attribute of a HTML element, and
                                performs a search-and-replace on certain values
      @param String selector  HTML element to match
      @param String attribute RegExp-escaped; HTML element attribute to match
      @param String front     RegExp-escaped; attribute value, prefix to match
      @param String flags     Optional RegExp flags, default "gi"
      @param String delimiter Optional RegExp-escaped; non-quote delimiters
      @param String end       Optional RegExp-escaped; forces the match to end
                                before an occurence of <end>
     */
    function cri(selector, attribute, front, flags, delimiter, end){
        if(typeof selector == "string") selector = new RegExp(selector, "gi");
        attribute = att + attribute;
        flags = typeof flags == "string" ? flags : "gi";
        var re1 = new RegExp('('+attribute+'\\s*=\\s*")([^"]*)', 'gi');
        var re2 = new RegExp("("+attribute+"\\s*=\\s*')([^']+)", 'gi');
        var at1 = new RegExp('('+front+')([^"]+)(")', flags);
        var at2 = new RegExp("("+front+")([^']+)(')", flags);
        if(typeof delimiter == "string"){
            end = typeof end == "string" ? end : "";
            var at3 = new RegExp("("+front+")([^\"'][^"+delimiter+"]*" + (end?"?)("+end+")":")()"), flags);
            var handleAttr = function(match, g1, g2){return g1+g2.replace(at1, by2).replace(at2, by2).replace(at3, by2)};
        } else {
            var handleAttr = function(match, g1, g2){return g1+g2.replace(at1, by2).replace(at2, by2)};
    }
        html = html.replace(selector, function(match){
             return match.replace(re1, handleAttr).replace(re2, handleAttr);
        });
    }

    /* <meta http-equiv=refresh content="  ; url= " > */
    cri("<meta"+any+att+"http-equiv\\s*=\\s*(?:\""+ae("refresh")+"\""+any+">|'"+ae("refresh")+"'"+any+">|"+ae("refresh")+"(?:"+ae(" ")+any+">|>))", "content", ae("url")+s+ae("=")+s, "i");

    cr("<"+any+att+"href\\s*="+any+">", "href"); /* Linked elements */
    cr("<form"+any+att+"action\\s*="+any+">", "action"); /* Form elements */
    cr("<"+any+att+"src\\s*="+any+">", "src"); /* Embedded elements */

    cr("<object"+any+att+"data\\s*="+any+">", "data"); /* <object data= > */
    cr("<applet"+any+att+"codebase\\s*="+any+">", "codebase"); /* <applet codebase= > */

    /* <param name=movie value= >*/
    cr("<param"+any+att+"name\\s*=\\s*(?:\""+ae("movie")+"\""+any+">|'"+ae("movie")+"'"+any+">|"+ae("movie")+"(?:"+ae(" ")+any+">|>))", "value");

    cr(/<style[^>]*>(?:[^"']*(?:"[^"]*"|'[^']*'))*?[^'"]*(?:<\/style|$)/gi, "url", "\\s*\\(\\s*", "", "\\s*\\)"); /* <style> */
    cri("<"+any+att+"style\\s*="+any+">", "style", ae("url")+s+ae("(")+s, 0, s+ae(")"), ae(")")); /*< style=" url(...) " > */
    return html;
};

function compressCSS(css) {
  return css
    .replace(/\s+/g, ' ')
    .replace(/:\s+/g, ':')
    .replace(/\/\*.*?\*\//g, '')
    .replace(/\} /g, '}')
    .replace(/ \{/g, '{')
    // .replace(/\{ /g, '{')
    .replace(/; /g, ';')
    .replace(/\n+/g, '');
}

function removeComments(element) {
  if (!element || !element.childNodes) return;
  var nodes = element.childNodes,
      i = nodes.length;
  
  while (i--) {
    if (nodes[i].nodeName === '#comment' && nodes[i].nodeValue.indexOf('[') !== 0) {
      element.removeChild(nodes[i]);
    }
    removeComments(nodes[i]);
  }
}

function Inliner(url, options, callback) {
  var root = url,
      inliner = this;

  this.requestCache = {};
  this.requestCachePending = {};
  
  // inherit EventEmitter so that we can send events with progress
  events.EventEmitter.call(this);

  if (typeof options == 'function') {
    callback = options;
    options = Inliner.defaults();
  } else if (options === undefined) {
    options = Inliner.defaults();
  }
  
  inliner.options = options;
  
  inliner.total = 1;
  inliner.todo = 1;
  inliner.emit('jobs', (inliner.total - inliner.todo) + '/' + inliner.total);

  inliner.on('error', function (data) {
    console.error(data + ' :: ' + url);
  });
  
  inliner.get(url, function (html) {
    inliner.todo--;
    inliner.emit('jobs', (inliner.total - inliner.todo) + '/' + inliner.total);
    
    // Replace relative urls with absolute
    if (url == rootUrl) {
      html = replace_all_rel_by_abs(html);
      debugger;
    }    
    
    
    // workaround for https://github.com/tmpvar/jsdom/issues/172
    // need to remove empty script tags as it casues jsdom to skip the env callback
    html = html.replace(/<\script(:? type=['"|].*?['"|])><\/script>/ig, '');

    if (!html) {
      inliner.emit('end', '');
      callback && callback('');
    } else {
      // BIG ASS PROTECTIVE TRY/CATCH - mostly because of this: https://github.com/tmpvar/jsdom/issues/319
      try { 

      jsdom.env(html, '', [
        'http://code.jquery.com/jquery.min.js'
      ], function(errors, window) {
        // remove jQuery that was included with jsdom
        window.$('script:last').remove();
        
        var todo = { scripts: true, images: inliner.options.images, links: true, styles: true },
            assets = {
              scripts: window.$('script'),
              images: window.$('img').filter(function(){ return this.src.indexOf('data:') == -1; }),
              links: window.$('link[rel=stylesheet]'),
              styles: window.$('style')
            },
            breakdown = {},
            images = {};
          
        inliner.total = 1;

        for (var key in todo) {
          if (todo[key] === true && assets[key]) {
            breakdown[key] = assets[key].length;
            inliner.total += assets[key].length;
            inliner.todo += assets[key].length;
          } else {
            assets[key] = [];
          }
        }

        inliner.emit('jobs', (inliner.total - inliner.todo) + '/' + inliner.total);

        function finished() {
          var items = 0,
              html = '';
          for (var key in breakdown) {
            items += breakdown[key];
          }
          inliner.emit('jobs', (inliner.total - inliner.todo) + '/' + inliner.total);

          if (items === 0) {
            // manually remove the comments
            var els = removeComments(window.document.documentElement);
            // collapse the white space
            if (inliner.options.collapseWhitespace) {
              // TODO put white space helper back in
              window.$('pre').html(function (i, html) {
                return html.replace(/\n/g, '~~nl~~'); //.replace(/\s/g, '~~s~~');
              });
              window.$('textarea').val(function (i, v) {
                return v.replace(/\n/g, '~~nl~~').replace(/\s/g, '~~s~~');
              });
              html = window.document.innerHTML;
              html = html.replace(/\s+/g, ' ').replace(/~~nl~~/g, '\n').replace(/~~s~~/g, ' ');
            } else {
              html = window.document.innerHTML;
            }

            html = '<!DOCTYPE html>' + html;
            callback && callback(html);
            inliner.emit('end', html);
          } else if (items < 0) {
            console.log('something went wrong on finish');
            console.dir(breakdown);
          } 
        }

        todo.images && assets.images.each(function () {
          var img = this,
              resolvedURL = URL.resolve(url, img.src);
          inliner.get(resolvedURL, { encode: true }, function (dataurl) {
            if (dataurl) images[img.src] = dataurl;
            img.src = dataurl;
            breakdown.images--;
            inliner.todo--;
            finished();
          });
        });
    
        todo.styles && assets.styles.each(function () {
          var style = this;
          inliner.getImportCSS(root, this.innerHTML, function (css, url) {
            inliner.getImagesFromCSS(url, css, function (css) {
              if (inliner.options.compressCSS) inliner.emit('progress', 'compress inline css');
              window.$(style).text(css);

              breakdown.styles--;
              inliner.todo--;
              finished();
            });
          });
        });

        todo.links && assets.links.each(function () {
          var link = this,
              linkURL = URL.resolve(url, link.href);

          inliner.get(linkURL, function (css) {
            inliner.getImagesFromCSS(linkURL, css, function (css) {
              inliner.getImportCSS(linkURL, css, function (css) {
                if (inliner.options.compressCSS) inliner.emit('progress', 'compress ' + linkURL);
                breakdown.links--;
                inliner.todo--;

                var style = '',
                    media = link.getAttribute('media');
            
                if (media) {
                  style = '<style>@media ' + media + '{' + css + '}</style>';
                } else {
                  style = '<style>' + css + '</style>';
                }

                window.$(link).replaceWith(style);
                finished();
              });
            });
          });
        });

        function scriptsFinished() {
          inliner.emit('jobs', (inliner.total - inliner.todo) + '/' + inliner.total);
          if (breakdown.scripts == 0) {
            // now compress the source JavaScript
            assets.scripts.each(function () {
              if (this.innerHTML.trim().length == 0) {
                // this is an empty script, so throw it away
                inliner.todo--;
                inliner.emit('jobs', (inliner.total - inliner.todo) + '/' + inliner.total);
                return;
              }

              var $script = window.$(this),
                  src = $script.attr('src'),
                  // note: not using .innerHTML as this coerses & => &amp;
                  orig_code = this.firstChild.nodeValue
                                  .replace(/<\/script>/gi, '<\\/script>'),
                  final_code = '';

              // only remove the src if we have a script body
              if (orig_code) { 
                $script.removeAttr('src');
              }

              // don't compress already minified code
              if(!(/\bmin\b/).test(src) && !(/google-analytics/).test(src)) { 
                inliner.todo++;
                inliner.total++;
                inliner.emit('jobs', (inliner.total - inliner.todo) + '/' + inliner.total);
                try {
                  var ast = jsp.parse(orig_code); // parse code and get the initial AST

                  ast = pro.ast_mangle(ast); // get a new AST with mangled names
                  ast = pro.ast_squeeze(ast); // get an AST with compression optimizations
                  final_code = pro.gen_code(ast);

                  // some protection against putting script tags in the body
                  window.$(this).text(final_code).append('\n');

                  if (src) {
                    inliner.emit('progress', 'compress ' + URL.resolve(root, src));
                  } else {
                    inliner.emit('progress', 'compress inline script');
                  }
                } catch (e) {
                  // console.error(orig_code.indexOf('script>script'));
                  // window.$(this).html(jsmin('', orig_code, 2));
                  console.error('exception on ', src);
                  console.error('exception in ' + src + ': ' + e.message);
                  console.error('>>>>>> ' + orig_code.split('\n')[e.line - 1]);
                }
                inliner.todo--;
                inliner.emit('jobs', (inliner.total - inliner.todo) + '/' + inliner.total);
              } else if (orig_code) {
                window.$(this).text(orig_code);
                // this.innerText = orig_code;
              }
            });
            finished();
          }
        }

        // basically this is the jQuery instance we tacked on to the request,
        // but we're just being extra sure before we do zap it out  
        todo.scripts && assets.scripts.each(function () {
          var $script = window.$(this),
              scriptURL = URL.resolve(url, this.src);

          if (!this.src || scriptURL.indexOf('google-analytics.com') !== -1) { // ignore google
            breakdown.scripts--;
            inliner.todo--;
            scriptsFinished();
          } else if (this.src) {
            inliner.get(scriptURL, { not: 'text/html' }, function (data) {
              // catches an exception that was being thrown, but script escaping wasn't being caught
              if (data) $script.text(data.replace(/<\/script>/gi, '<\\/script>')); //.replace(/\/\/.*$\n/g, ''));
              // $script.before('<!-- ' + scriptURL + ' -->');
              breakdown.scripts--;
              inliner.todo--;
              scriptsFinished();
            });      
          }
        });

        // edge case - if there's no images, nor scripts, nor links - we call finished manually
        if (assets.links.length == 0 && 
            assets.styles.length == 0 && 
            assets.images.length == 0 && 
            assets.scripts.length == 0) {
          finished();
        }
        
        /** Inliner jobs:
         *  1. get all inline images and base64 encode
         *  2. get all external style sheets and move to inline
         *  3. get all image references in CSS and base64 encode and replace urls
         *  4. get all external scripts and move to inline
         *  5. compress JavaScript
         *  6. compress CSS & support media queries
         *  7. compress HTML (/>\s+</g, '> <');
         * 
         *  FUTURE ITEMS:
         *  - support for @import
         *  - javascript validation - i.e. not throwing errors
         */
      });

      } catch (e) {
        inliner.emit('error', 'Fatal error parsing HTML - exiting');
      }
    }
  });
}

util.inherits(Inliner, events.EventEmitter);

Inliner.version = Inliner.prototype.version = JSON.parse(require('fs').readFileSync(__dirname + '/package.json').toString()).version;

Inliner.prototype.get = function (url, options, callback) {
  // support no options being passed in
  if (typeof options == 'function') {
    callback = options;
    options = {};
  }
  
  // if we've cached this request in the past, just return the cached content
  if (this.requestCache[url] !== undefined) {
    this.emit('progress', 'cached ' + url);
    return callback && callback(this.requestCache[url]);
  } else if (this.requestCachePending[url] !== undefined) {
    this.requestCachePending[url].push(callback);
    return true;
  } else {
    this.requestCachePending[url] = [callback];
  }

  var inliner = this;

  // TODO remove the sync
  if (path.existsSync(url)) {
    // then we're dealing with a file
    fs.readFile(url, 'utf8', function (err, body) {
      inliner.requestCache[url] = body;
      inliner.requestCachePending[url].forEach(function (callback, i) {
        if (i == 0 && body) {
          inliner.emit('progress', (options.encode ? 'encode' : 'get') + ' ' + url);
        } else if (body) {
          inliner.emit('progress', 'cached ' + url);
        }
        callback && callback(body);
      });
    });
    
    return;
  }
  
  // otherwis continue and create a new web request
  var request = makeRequest(url),
      body = '';

  // this tends to occur when we can't connect to the url - i.e. target is down
  // note that the main inliner app handles sending the error back to the client
  request.on('error', function (error) {
    console.error(error.message, url);
    callback && callback('');
  });


  request.on('response', function (res) {
    var gunzip;

    // if we get a gzip header, then first we attempt to load the node-compress library
    // ...which annoyingly isn't supported anymore (maybe I should fork it...).
    // once loaded, we set up event listeners to handle data coming in and do a little
    // dance with the response object - which I'll explain... ==>
    if (res.headers['content-encoding'] == 'gzip') {
      console.error('loading gzip library');
      if (compress === null) {
        try {
          compress = require('./node-compress/lib/compress/');
        } catch (e) {
          console.error(url + ' sent gzipped header\nFailed to load node-compress - see http://github.com/remy/inliner for install directions. \nexiting');
          process.exit();
        }
      }
      gunzip = new compress.GunzipStream();
      
      // the data event is triggered by writing to the gunzip object when the response
      // receives data (yeah, further down).
      // once all the data has finished (triggerd by the response end event), we undefine
      // the gunzip object and re-trigger the response end event. By this point, we've
      // decompressed the gzipped content, and it's human readable again.
      gunzip.on('data', function (chunk) {
        body += chunk;
      }).on('end', function () {
        gunzip = undefined;
        res.emit('end');
      });
    }
    
    res.on('data', function (chunk) {
      // only process data if we have a 200 ok
      if (res.statusCode == 200) {
        if (gunzip) {
          gunzip.write(chunk);
        } else {
          body += chunk;
        }
      }
    });
    
    // required if we're going to base64 encode the content later on
    if (options.encode) {
      res.setEncoding('binary');
    }

    res.on('end', function () { 
      if (gunzip) {
        gunzip.end();
        return;
      } 

      if (res.statusCode !== 200) {
        inliner.emit('progress', 'get ' + res.statusCode + ' on ' + url);
        body = ''; // ?
      } else if (res.headers['location']) {
        return inliner.get(res.headers['location'], options, callback);
      } else {
        if (options && options.not) {
          if (res.headers['content-type'].indexOf(options.not) !== -1) {
            body = '';
          }
        }
        
        if (options.encode && res.statusCode == 200) {
          body = 'data:' + res.headers['content-type'] + ';base64,' + new Buffer(body, 'binary').toString('base64');
        }
        
        inliner.requestCache[url] = body;
        inliner.requestCachePending[url].forEach(function (callback, i) {
          if (i == 0 && body && res.statusCode == 200) {
            inliner.emit('progress', (options.encode ? 'encode' : 'get') + ' ' + url);
          } else if (body) {
            inliner.emit('progress', 'cached ' + url);
          }
          callback && callback(body);
        });
      }
    });
  }).end();
};

Inliner.prototype.getImagesFromCSS = function (rooturl, rawCSS, callback) {
  if (this.options.images === false) {
    callback && callback(rawCSS);
    return;
  }
  
  var inliner = this,
      images = {},
      urlMatch = /url\((?:['"]*)(?!['"]*data:)(.*?)(?:['"]*)\)/g,
      singleURLMatch = /url\(\s*(?:['"]*)(?!['"]*data:)(.*?)(?:['"]*)\s*\)/,
      matches = rawCSS.match(urlMatch),
      imageCount = matches === null ? 0 : matches.length; // TODO check!
  
  inliner.total += imageCount;
  inliner.todo += imageCount;
  
  function checkFinished() {
    inliner.emit('jobs', (inliner.total - inliner.todo) + '/' + inliner.total);
    if (imageCount < 0) {
      console.log('something went wrong :-S');
    } else if (imageCount == 0) {
      callback(rawCSS.replace(urlMatch, function (m, url) {
        return 'url(' + images[url] + ')';
      }));
    }
  }
  
  if (imageCount) {
    matches.forEach(function (url) {
      url = url.match(singleURLMatch)[1];
      var resolvedURL = URL.resolve(rooturl, url);
      if (images[url] === undefined) {
        inliner.get(resolvedURL, { encode: true }, function (dataurl) {
          imageCount--;
          inliner.todo--;
          if (images[url] === undefined) images[url] = dataurl;
          
          checkFinished();
        });
      } else {
        imageCount--;
        inliner.todo--;
        checkFinished();
      }
    });
  } else {
    callback(rawCSS);
  }
};

Inliner.prototype.getImportCSS = function (rooturl, css, callback) {
  // if (typeof css == 'function') {
  //   callback = css;
  //   rooturl = '';
  // }
  
  var position = css.indexOf('@import'),
      inliner = this;

  if (position !== -1) {
    var match = css.match(/@import\s*(.*)/);
    
    if (match !== null && match.length) {
      var url = match[1].replace(/url/, '').replace(/['}"]/g, '').replace(/;/, '').trim().split(' '); // clean up
      // if url has a length > 1, then we have media types to target
      var resolvedURL = URL.resolve(rooturl, url[0]);
      inliner.get(resolvedURL, function (importedCSS) {
        inliner.emit('progress', 'import ' + resolvedURL);
        if (url.length > 1) {
          url.shift();
          importedCSS = '@media ' + url.join(' ') + '{' + importedCSS + '}';
        }
        
        css = css.replace(match[0], importedCSS);
        inliner.getImportCSS(rooturl, css, callback);
      });          
    }
  } else {
    if (inliner.options.compressCSS) css = compressCSS(css);
    callback(css, rooturl);
  }
};

Inliner.defaults = function () { return { compressCSS: true, collapseWhitespace: true, images: true }; };

var makeRequest = Inliner.makeRequest = function (url, extraOptions) {
  var oURL = URL.parse(url),
      options = {
        host: oURL.hostname,
        port: oURL.port === undefined ? (oURL.protocol+'').indexOf('https') === 0 ? 443 : 80 : oURL.port,
        path: (oURL.pathname || '/') + (oURL.search || ''), // note 0.5.0pre doesn't fill pathname if missing
        method: 'GET'
      };

  for (var key in extraOptions) {
    options[key] = extraOptions[key];
  }

  return http[oURL.protocol.slice(0, -1) || 'http'].request(options);
};

module.exports = Inliner;

if (!module.parent) {
  // if this module isn't being included in a larger app, defer to the 
  // bin/inliner for the help options
  require('./bin/inliner');
}
